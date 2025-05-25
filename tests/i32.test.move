#[test_only]
module move_int::i32_test {
    use move_int::i32::{as_u32, from, from_u32, neg_from, abs, add, sub, mul,
        div, wrapping_add, wrapping_sub, pow, sign, cmp, min, max,
        eq, gt, lt, gte, lte, and, or, is_zero, is_neg, zero, mod
    };

    // Constants for testing
    const OVERFLOW: u64 = 0;
    const BITS_MIN_I32: u32 = 1 << 31;
    const BITS_MAX_I32: u32 = 0x7fffffff;
    const LT: u8 = 0;
    const EQ: u8 = 1;
    const GT: u8 = 2;

    // === Construction Tests ===
    #[test]
    fun test_constructors() {
        // Test zero()
        let zero_val = zero();
        assert!(as_u32(zero_val) == 0, 0);
        assert!(sign(zero_val) == 0, 1);
        assert!(is_zero(zero_val), 2);

        // Test from()
        assert!(as_u32(from(0)) == 0, 3);
        assert!(as_u32(from(10)) == 10, 4);
        assert!(as_u32(from(BITS_MAX_I32)) == BITS_MAX_I32, 5);

        // Test from_u32()
        assert!(as_u32(from_u32(42)) == 42, 6);
        assert!(as_u32(from_u32(BITS_MIN_I32)) == BITS_MIN_I32, 7);
        assert!(sign(from_u32(BITS_MIN_I32)) == 1, 8);

        // Test neg_from()
        assert!(as_u32(neg_from(0)) == 0, 9);
        assert!(as_u32(neg_from(1)) == 0xffffffff, 10);
        assert!(as_u32(neg_from(BITS_MIN_I32)) == BITS_MIN_I32, 11);
        assert!(as_u32(neg_from(0x7fffffff)) == 0x80000001, 12);
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_from_overflow() {
        from(BITS_MIN_I32);
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_neg_from_overflow() {
        neg_from(0x80000001);
    }

    // === Arithmetic Operation Tests ===
    #[test]
    fun test_basic_arithmetic() {
        // Test wrapping_add
        assert!(
            as_u32(wrapping_add(from(10), from(20))) == 30,
            0
        );
        assert!(
            as_u32(wrapping_add(from(BITS_MAX_I32), from(1))) == BITS_MIN_I32,
            1
        );
        assert!(
            as_u32(
                wrapping_add(from(BITS_MAX_I32 - 1), from(1))
            ) == BITS_MAX_I32,
            2
        );

        // Test wrapping_sub
        assert!(
            as_u32(wrapping_sub(from(20), from(10))) == 10,
            3
        );
        assert!(
            as_u32(wrapping_sub(from(0), from(1))) == as_u32(neg_from(1)),
            4
        );
        assert!(
            as_u32(wrapping_sub(from(1), neg_from(1))) == as_u32(from(2)),
            5
        );

        // Test add/sub without overflow
        assert!(as_u32(add(from(15), from(25))) == 40, 6);
        assert!(as_u32(sub(from(25), from(15))) == 10, 7);
        assert!(as_u32(add(neg_from(1), from(1))) == 0, 8);

        // Test multiplication
        assert!(as_u32(mul(from(10), from(10))) == 100, 9);
        assert!(
            as_u32(mul(neg_from(10), from(10))) == as_u32(neg_from(100)),
            10
        );
        assert!(
            as_u32(mul(from(BITS_MIN_I32 / 2), neg_from(2)))
                == as_u32(neg_from(BITS_MIN_I32)),
            11
        );

        // Test division
        assert!(as_u32(div(from(100), from(10))) == 10, 12);
        assert!(
            as_u32(div(from(10), neg_from(1))) == as_u32(neg_from(10)),
            13
        );
        assert!(
            as_u32(div(neg_from(10), neg_from(1))) == 10,
            14
        );

        // Test mod
        assert!(eq(mod(neg_from(3), from(3)), zero()), 15);
        assert!(eq(mod(neg_from(4), from(3)), neg_from(1)), 16);
        assert!(eq(mod(neg_from(5), from(3)), neg_from(2)), 17);
        assert!(eq(mod(neg_from(6), from(3)), zero()), 18);
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_add_overflow() {
        add(from(BITS_MAX_I32), from(1));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_add_underflow() {
        add(neg_from(BITS_MIN_I32), neg_from(1));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_sub_overflow() {
        sub(from(BITS_MAX_I32), neg_from(1));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_sub_underflow() {
        sub(neg_from(BITS_MIN_I32), from(1));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_mul_overflow() {
        mul(from(0x10000), from(0x10000));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_mul_overflow_negative() {
        mul(neg_from(0x10000), neg_from(0x10000));
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_div_overflow() {
        div(neg_from(BITS_MIN_I32), neg_from(1));
    }

    // === Advanced Math Operation Tests ===
    #[test]
    fun test_advanced_operations() {
        // Test pow
        assert!(eq(pow(from(2), 3), from(8)), 0);
        assert!(eq(pow(neg_from(2), 3), neg_from(8)), 1);
        assert!(eq(pow(from(2), 0), from(1)), 2);
        assert!(eq(pow(neg_from(2), 2), from(4)), 3);
        assert!(eq(pow(from(1), 100), from(1)), 4);
    }

    // === Comparison Tests ===
    #[test]
    fun test_comparisons() {
        // Test cmp with all sign combinations
        assert!(cmp(neg_from(2), neg_from(1)) == LT, 0); // neg vs neg
        assert!(cmp(neg_from(1), neg_from(1)) == EQ, 1); // neg equal
        assert!(cmp(neg_from(1), neg_from(2)) == GT, 2); // neg vs neg
        assert!(cmp(neg_from(1), from(0)) == LT, 3); // neg vs pos
        assert!(cmp(from(0), neg_from(1)) == GT, 4); // pos vs neg
        assert!(cmp(from(1), from(2)) == LT, 5); // pos vs pos
        assert!(cmp(from(2), from(2)) == EQ, 6); // pos equal
        assert!(cmp(from(2), from(1)) == GT, 7); // pos vs pos

        // Test min with all branches
        assert!(
            eq(
                min(neg_from(2), neg_from(1)),
                neg_from(2)
            ),
            8
        );
        assert!(
            eq(min(neg_from(1), from(0)), neg_from(1)),
            9
        );
        assert!(
            eq(min(from(0), neg_from(1)), neg_from(1)),
            10
        );
        assert!(
            eq(min(from(BITS_MAX_I32), from(0)), from(0)),
            11
        );
        assert!(
            eq(
                min(neg_from(BITS_MIN_I32), from(0)),
                neg_from(BITS_MIN_I32)
            ),
            12
        );

        // Test max with all branches
        assert!(
            eq(
                max(neg_from(2), neg_from(1)),
                neg_from(1)
            ),
            13
        );
        assert!(
            eq(max(neg_from(1), from(0)), from(0)),
            14
        );
        assert!(
            eq(max(from(0), neg_from(1)), from(0)),
            15
        );
        assert!(
            eq(
                max(from(BITS_MAX_I32), from(0)),
                from(BITS_MAX_I32)
            ),
            16
        );
        assert!(
            eq(
                max(neg_from(BITS_MIN_I32), from(0)),
                from(0)
            ),
            17
        );
    }

    // === Bitwise Operation Tests ===
    #[test]
    fun test_bitwise_ops() {
        // Test OR
        assert!(
            as_u32(or(from(0x0F), from(0xF0))) == 0xFF,
            0
        );
        assert!(as_u32(or(from(0), from(0))) == 0, 1);
        assert!(
            as_u32(or(from(BITS_MAX_I32), from(0))) == BITS_MAX_I32,
            2
        );

        // Test AND
        assert!(
            as_u32(and(from(0x0F), from(0xFF))) == 0x0F,
            3
        );
        assert!(
            as_u32(and(from(0xFF), from(0xFF))) == 0xFF,
            4
        );
        assert!(as_u32(and(from(0), from(0xFF))) == 0, 5);
    }

    // === Helper Function Tests ===
    #[test]
    fun test_helper_functions() {
        // Test abs
        assert!(as_u32(abs(from(10))) == 10, 0);
        assert!(as_u32(abs(neg_from(10))) == 10, 1);
        assert!(as_u32(abs(neg_from(0))) == 0, 2);

        // Test sign and is_neg
        assert!(sign(neg_from(10)) == 1, 3);
        assert!(sign(from(10)) == 0, 4);
        assert!(is_neg(neg_from(1)), 5);
        assert!(!is_neg(from(1)), 6);
        assert!(!is_neg(zero()), 7);

        // Test comparison operators
        assert!(gt(from(10), from(5)), 8);
        assert!(lt(from(5), from(10)), 9);
        assert!(gte(from(5), from(5)), 10);
        assert!(lte(from(5), from(5)), 11);
        assert!(!gt(from(5), from(5)), 12);
        assert!(!lt(from(5), from(5)), 13);
    }

    #[test]
    #[expected_failure(abort_code = 0, location = move_int::i32)]
    fun test_abs_overflow() {
        abs(neg_from(BITS_MIN_I32));
    }
}
