module move_int::i64 {
    spec module {
        pragma aborts_if_is_strict;
    }

    /// Interprets the I64 `bits` field as a signed integer.
    spec fun to_num(i: I64): num {
        // Check sign bit (bit 63): if set, value is negative
        if (i.bits >= TWO_POW_63) {
            // Interpret bits as two's complement negative number
            (i.bits as num) - MAX_U64_PLUS_ONE
        } else {
            (i.bits as num)
        }
    }

    const OVERFLOW: u64 = 0;
    const DIVISION_BY_ZERO: u64 = 1;

    /// min number that a I64 could represent = (1 followed by 63 0s) = 1 << 63
    const BITS_MIN_I64: u64 = 1 << 63;

    /// max number that a I64 could represent = (0 followed by 63 1s) = (1 << 63) - 1
    const BITS_MAX_I64: u64 = 0x7fffffffffffffff;

    const TWO_POW_63: u64 = 9223372036854775808;

    /// (1 << 64) - 1
    const MAX_U64: u64 = 18446744073709551615;

    /// 1 << 64
    const MAX_U64_PLUS_ONE: u128 = 18446744073709551616;

    const LT: u8 = 0;
    const EQ: u8 = 1;
    const GT: u8 = 2;

    struct I64 has copy, drop, store {
        bits: u64
    }

    /// Creates an I64 from a u64, asserting that it's not greater than the maximum positive value
    public fun from(v: u64): I64 {
        assert!(v <= BITS_MAX_I64, OVERFLOW);
        I64 { bits: v }
    }

    spec from {
        aborts_if v > BITS_MAX_I64 with OVERFLOW;
    }

    /// Creates a negative I64 from a u64, asserting that it's not greater than the minimum negative value
    public fun neg_from(v: u64): I64 {
        assert!(v <= BITS_MIN_I64, OVERFLOW);
        I64 { bits: twos_complement(v) }
    }

    spec neg_from {
        aborts_if v > BITS_MIN_I64 with OVERFLOW;

        // from(v) + neg_from(v) == 0
        ensures is_zero(add(result, from(v)));
    }

    /// Performs wrapping addition on two I64 numbers
    public fun wrapping_add(num1: I64, num2: I64): I64 {
        I64 { bits: (((num1.bits as u128) + (num2.bits as u128)) % MAX_U64_PLUS_ONE as u64) }
    }

    spec wrapping_add {
        ensures result.bits == (num1.bits + num2.bits) % MAX_U64_PLUS_ONE;
    }

    /// Performs checked addition on two I64 numbers, abort on overflow
    public fun add(num1: I64, num2: I64): I64 {
        let sum = wrapping_add(num1, num2);
        // overflow only if: (1) postive + postive = negative, OR (2) negative + negative = positive
        let is_num1_neg = is_neg(num1);
        let is_num2_neg = is_neg(num2);
        let is_sum_neg = is_neg(sum);
        let overflow = (is_num1_neg && is_num2_neg && !is_sum_neg) || (!is_num1_neg && !is_num2_neg && is_sum_neg);
        assert!(!overflow, OVERFLOW);
        sum
    }
    spec add {
        pragma opaque;

        // Abort conditions
        // Overflow when: two positives yield negative, or two negatives yield positive
        aborts_if !is_neg(num1) && !is_neg(num2) && is_neg(wrapping_add(num1, num2)) with OVERFLOW;
        aborts_if is_neg(num1) && is_neg(num2) && !is_neg(wrapping_add(num1, num2)) with OVERFLOW;

        // Inverse property
        // add(a, -a) = 0
        ensures eq(abs(num1), abs(num2)) && sign(num1) != sign(num2) ==> is_zero(result);

        // Identity properties
        ensures is_zero(num2) ==> eq(result, num1);
        ensures is_zero(num1) ==> eq(result, num2);

        // Soundness: result equals num1 + num2 in num domain
        ensures to_num(result) == to_num(num1) + to_num(num2);
    }

    /// Performs wrapping subtraction on two I64 numbers
    public fun wrapping_sub(num1: I64, num2: I64): I64 {
        wrapping_add(num1, I64 { bits: twos_complement(num2.bits) })
    }

    spec wrapping_sub {
        ensures result.bits == (num1.bits + twos_complement(num2.bits)) % MAX_U64_PLUS_ONE;
    }

    /// Performs checked subtraction on two I64 numbers, asserting on overflow
    public fun sub(num1: I64, num2: I64): I64 {
        add(num1, I64 { bits: twos_complement(num2.bits) })
    }
    spec sub {
        // Function aborts if subtraction would overflow
        aborts_if !is_neg(num1) && !is_neg(from(twos_complement(num2.bits))) && is_neg(wrapping_add(num1, from(twos_complement(num2.bits)))) with OVERFLOW;
        aborts_if is_neg(num1) &&  is_neg(from(twos_complement(num2.bits))) && !is_neg(wrapping_add(num1, from(twos_complement(num2.bits)))) with OVERFLOW;

        // Subtracting zero returns the original number
        ensures is_zero(num1) ==> result.bits == twos_complement(num2.bits);
        ensures is_zero(num2) ==> eq(result, num1);

        // Subtracting a number from itself gives zero
        ensures eq(num1, num2) ==> is_zero(result);

        // Subtraction behaves like adding the negative in num space
        ensures to_num(result) == to_num(num1) + to_num(from(twos_complement(num2.bits)));
    }

    /// Performs multiplication on two I64 numbers
    public fun mul(num1: I64, num2: I64): I64 {
        let product = (abs_u64(num1) as u128) * (abs_u64(num2) as u128);
        if (sign(num1) != sign(num2)) {
            assert!(product <= (BITS_MIN_I64 as u128), OVERFLOW);
            neg_from((product as u64))
        } else {
            assert!(product <= (BITS_MAX_I64 as u128), OVERFLOW);
            from((product as u64))
        }
    }

    spec mul {
        // Abort conditions
        // If result should be negative (opposite signs), must not exceed abs(MIN_I64)
        aborts_if sign(num1) != sign(num2) &&
            (abs_u64(num1) as u128) * (abs_u64(num2) as u128) > (BITS_MIN_I64 as u128)
            with OVERFLOW;

        // If result should be positive (same signs), must not exceed MAX_I64
        aborts_if sign(num1) == sign(num2) &&
            (abs_u64(num1) as u128) * (abs_u64(num2) as u128) > (BITS_MAX_I64 as u128)
            with OVERFLOW;

        // result is positive, sign(num1) == sign(num2)
        ensures !is_neg(result) && !is_zero(result) ==> sign(num1) == sign(num2);

        // result is negative, sign(num1) != sign(num2)
        ensures is_neg(result) && !is_zero(result) ==> sign(num1) != sign(num2);

        // result is 0, num1 is zero or num2 is zero
        ensures is_zero(result) ==> is_zero(num1) || is_zero(num2);

        // Behavior guarantees
        ensures eq(result, mul(num2, num1));
        ensures to_num(result) == to_num(num1) * to_num(num2);
    }

    /// Performs division on two I64 numbers
    /// Note that we mimic the behavior of solidity int division that it rounds towards 0 rather than rounds down
    /// - rounds towards 0: (-4) / 3 = -(4 / 3) = -1 (remainder = -1)
    /// - rounds down: (-4) / 3 = -2 (remainder = 2)
    public fun div(num1: I64, num2: I64): I64 {
        assert!(!is_zero(num2), DIVISION_BY_ZERO);
        let result = abs_u64(num1) / abs_u64(num2);
        if (sign(num1) != sign(num2)) neg_from(result)
        else from(result)
    }
    spec div {
        pragma opaque;

        // Abort conditions
        aborts_if is_zero(num2) with DIVISION_BY_ZERO;

        // MIN_I64 / -1 = MAX_I64 + 1, which is too big to fit in an I64
        aborts_if sign(num1) == sign(num2) && abs_u64(num1) / abs_u64(num2) > BITS_MAX_I64 with OVERFLOW;
        aborts_if sign(num1) != sign(num2) && abs_u64(num1) / abs_u64(num2) > BITS_MIN_I64 with OVERFLOW;

        // Behavior guarantees
        // Division result always rounds toward zero.
        // The result multiplied back gives the truncated part of num1
        ensures !is_zero(num2) ==>
            to_num(num1) == to_num(result) * to_num(num2) + to_num(mod(num1, num2));

        // Zero divided by anything is zero
        ensures is_zero(num1) ==> is_zero(result);

        // Sign correctness
        // result is positive, sign(num1) == sign(num2)
        ensures !is_neg(result) && !is_zero(result) ==> sign(num1) == sign(num2);
        // result is negative, sign(num1) != sign(num2)
        ensures is_neg(result) && !is_zero(result) ==> sign(num1) != sign(num2);

        // Always round down
        // if num1 is positive, mul(num2, result) <= num1
        ensures !is_neg(num1) ==> lte(mul(num2, result), num1);
        // if num1 is negative, mul(num2, result) >= num1
        ensures is_neg(num1) ==> gte(mul(num2, result), num1);
    }

    /// Performs modulo on two I64 numbers
    /// a mod b = a - b * (a / b)
    // TODO: Spec method
    public fun mod(num1: I64, num2: I64): I64 {
        let quotient = div(num1, num2);
        sub(num1, mul(num2, quotient))
    }

    /// Returns the absolute value of an I64 number
    public fun abs(v: I64): I64 {
        let bits = if (sign(v) == 0) { v.bits }
        else {
            assert!(v.bits > BITS_MIN_I64, OVERFLOW);
            twos_complement(v.bits)
        };
        I64 { bits }
    }

    spec abs {
        aborts_if is_neg(v) && v.bits <= BITS_MIN_I64 with OVERFLOW;
        ensures is_neg(v) ==> is_zero(add(abs(v), v));
        ensures !is_neg(v) ==> abs(v).bits == v.bits;

        ensures !is_neg(v) ==> eq(abs(v), v);
    }

    /// Returns the absolute value of an I64 number as a u64
    public fun abs_u64(v: I64): u64 {
        if (sign(v) == 0) v.bits
        else twos_complement(v.bits)
    }
    spec abs_u64 {
        aborts_if is_neg(v) && v.bits < BITS_MIN_I64 with OVERFLOW;

        ensures is_neg(v) ==> result == twos_complement(v.bits);
        ensures !is_neg(v) ==> result == v.bits;
    }

    /// Returns the minimum of two I64 numbers
    public fun min(a: I64, b: I64): I64 {
        if (lt(a, b)) a else b
    }
    spec min {
        ensures to_num(a) <= to_num(b) ==> to_num(result) == to_num(a);
        ensures to_num(a) > to_num(b) ==> to_num(result) == to_num(b);
    }

    /// Returns the maximum of two I64 numbers
    public fun max(a: I64, b: I64): I64 {
        if (gt(a, b)) a else b
    }
    spec max {
        ensures to_num(a) >= to_num(b) ==> to_num(result) == to_num(a);
        ensures to_num(a) < to_num(b) ==> to_num(result) == to_num(b);
    }

    /// Raises an I64 number to a u64 power
    // TODO: Spec method that plays nicely with loops ("enter loop, variable(s) base, exponent, result havocked and reassigned")
    public fun pow(base: I64, exponent: u64): I64 {
        if (exponent == 0) {
            return from(1)
        };
        let result = from(1);
        while (exponent > 0)  {
            if (exponent & 1 == 1) {
                result = mul(result, base);
            };
            base = mul(base, base);
            exponent >>= 1;
        };
        result
    }

    /// Creates an I64 from a u64 without any checks
    public fun pack(v: u64): I64 {
        I64 { bits: v }
    }

    /// Get internal bits of I64
    public fun unpack(v: I64): u64 {
        v.bits
    }

    /// Returns the sign of an I64 number (0 for positive, 1 for negative)
    public fun sign(v: I64): u8 {
        ((v.bits / TWO_POW_63) as u8)
    }
    spec sign {
        // Result must be 0 or 1 (unsigned 8-bit)
        ensures result == 0 || result == 1;

        // If the number is negative, sign is 1
        ensures is_neg(v) ==> result == 1;

        // If the number is non-negative, sign is 0
        ensures !is_neg(v) ==> result == 0;
    }

    /// Creates and returns an I64 representing zero
    public fun zero(): I64 {
        I64 { bits: 0 }
    }
    spec zero {
        // The result must have zero bits
        ensures is_zero(result);

        // The result is not negative
        ensures !is_neg(result);

        // The result is equal to itself by to_num
        ensures to_num(result) == 0;

        // Negative zero is zero
        ensures eq(neg_from(0), zero());
    }

    /// Checks if an I64 number is zero
    public fun is_zero(v: I64): bool {
        v.bits == 0
    }
    spec is_zero {
        // Returns true iff the bit representation is 0
        ensures result == (v.bits == 0);

        // If the number is zero, to_num is 0
        ensures result ==> to_num(v) == 0;

        // If the number is not zero, to_num is non-zero
        ensures !result ==> to_num(v) != 0;
    }

    /// Checks if an I64 number is negative
    public fun is_neg(v: I64): bool {
        sign(v) == 1
    }
    spec is_neg {
        // Directly linked to the sign function
        ensures result == (sign(v) == 1);

        // If result is true, the number is negative in two's complement
        ensures result ==> v.bits >= TWO_POW_63;

        // If result is false, the number is non-negative
        ensures !result ==> v.bits < TWO_POW_63;
    }

    /// Compares two I64 numbers, returning LT, EQ, or GT
    public fun cmp(num1: I64, num2: I64): u8 {
        let sign1 = sign(num1);
        let sign2 = sign(num2);

        if (num1.bits == num2.bits) {
            EQ
        } else if (sign1 > sign2) {
            LT
        } else if (sign1 < sign2) {
            GT
        } else if (num1.bits > num2.bits) {
            GT
        } else {
            LT
        }
    }
    spec cmp {
        // Result must be one of LT, EQ, or GT
        ensures result == LT || result == EQ || result == GT;

        // Equality case
        ensures num1.bits == num2.bits ==> result == EQ;

        // Negative vs positive
        ensures sign(num1) > sign(num2) ==> result == LT;
        ensures sign(num1) < sign(num2) ==> result == GT;

        // Same sign, different magnitude
        ensures sign(num1) == sign(num2) && num1.bits > num2.bits ==> result == GT;
        ensures sign(num1) == sign(num2) && num1.bits < num2.bits ==> result == LT;
    }

    /// Checks if two I64 numbers are equal
    public fun eq(num1: I64, num2: I64): bool {
        cmp(num1, num2) == EQ
    }
    spec eq {
        // Result is true iff both are bitwise equal
        ensures result == (num1.bits == num2.bits);

        // Equivalence with cmp
        ensures result == (cmp(num1, num2) == EQ);
    }

    /// Checks if the first I64 number is greater than the second
    public fun gt(num1: I64, num2: I64): bool {
        cmp(num1, num2) == GT
    }
    spec gt {
        // Result is true iff cmp returns GT
        ensures result == (cmp(num1, num2) == GT);

        // If gt is true, then not equal
        ensures result ==> !eq(num1, num2);
    }

    /// Checks if the first I64 number is greater than or equal to the second
    public fun gte(num1: I64, num2: I64): bool {
        cmp(num1, num2) >= EQ
    }
    spec gte {
        // Only returns true if num1 is equal to or greater than num2
        ensures result == (cmp(num1, num2) == EQ || cmp(num1, num2) == GT);
        // Never returns true if num1 < num2
        ensures cmp(num1, num2) == LT ==> result == false;
    }

    /// Checks if the first I64 number is less than the second
    public fun lt(num1: I64, num2: I64): bool {
        cmp(num1, num2) == LT
    }
    spec lt {
        // Only returns true if num1 is strictly less than num2
        ensures result == (cmp(num1, num2) == LT);
        // Never returns true if num1 >= num2
        ensures (cmp(num1, num2) == EQ || cmp(num1, num2) == GT) ==> result == false;
    }

    /// Checks if the first I64 number is less than or equal to the second
    public fun lte(num1: I64, num2: I64): bool {
        cmp(num1, num2) <= EQ
    }
    spec lte {
        // Only returns true if num1 is equal to or less than num2
        ensures result == (cmp(num1, num2) == EQ || cmp(num1, num2) == LT);
        // Never returns true if num1 > num2
        ensures cmp(num1, num2) == GT ==> result == false;
    }

    /// Two's complement in order to dervie negative representation of bits
    /// It is overflow-proof because we hardcode 2's complement of 0 to be 0
    /// Which is fine for our specific use case
    fun twos_complement(v: u64): u64 {
        if (v == 0) 0
        // (1 << 64) - v
        else MAX_U64 - v + 1
    }

    spec twos_complement {
        ensures v == 0 ==> result == 0;
        ensures v > 0 ==> result + v == MAX_U64_PLUS_ONE;
    }

    #[test_only]
    fun twos_complement_for_test(v: u64): u64 {
        twos_complement(v)
    }
}
