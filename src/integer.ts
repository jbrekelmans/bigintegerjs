import {assert, isIntegralDouble, RoundingMode, double_log10, double_roundToZero } from "esbasejs";
import { DoubleUtilities } from "ieee754js";

let double_pow = Math.pow;
let double_ceil = Math.ceil;
let double_floor = Math.floor;
let double_max = Math.max;
let double_abs = Math.abs;
let double_posInf = Number.POSITIVE_INFINITY;
let double_negInf = -double_posInf;
let double_notANumber = Number.NaN;
let doubleUtil = DoubleUtilities.getInstance();
let doubleUtil_mantissaSize_base2 = doubleUtil.getMantissaSize_base2();
let doubleUtil_2PowMantNoBits = double_pow(2, doubleUtil_mantissaSize_base2);
let doubleUtil_expMaxMinusMantNoBits = doubleUtil.getExponentMax() - doubleUtil_mantissaSize_base2;

function doubleUtil_incMantAndCreate(exp, mant, isNegative): number {
    mant += 1;
    if (doubleUtil_2PowMantNoBits <= mant) {
        mant = mant * 0.5;
        exp += 1;
        if (doubleUtil_expMaxMinusMantNoBits <= exp) {
            return isNegative ? double_negInf : double_posInf;
        }
    }
    return doubleUtil.create(exp, mant, isNegative);
}

let digBase_log2 = 26;
let readOnlyArr_pow2: number[] = new Array(digBase_log2);
readOnlyArr_pow2[0] = 1;
for (let i = 1; i < digBase_log2; i++) {
    readOnlyArr_pow2[i] = readOnlyArr_pow2[i - 1] * 2;
}
// Used in _divMod_ll
let readOnlyArr_len1: number[] = [0];
let digBase = double_pow(2, digBase_log2);
let digBase_reciprocal = double_pow(2, -digBase_log2);
let digMax = digBase - 1;
let digMax_log10 = double_floor(double_log10(digMax));

assert(digBase_log2 <= 30);
assert((digBase & (digBase - 1)) === 0);
function dig_noMostSignificantZeroBits(v: number): number {
    assert(isIntegralDouble(v));
    assert(v !== 0);
    let c = 0;
    // 26 bits remaining
    if ((v & 0x3FFE000) === 0) {
        c += 13;
        v <<= 13;
    }
    // 13 bits remaining
    if ((v & 0x3F00000) === 0) {
        c += 6;
        v <<= 6;
    }
    // 7 bits remaining
    if ((v & 0x3C00000) === 0) {
        c += 4;
        v <<= 4;
    }
    // 3 bits remaining
    if ((v & 0x3000000) === 0) {
        c += 2;
        v <<= 2;
    }
    if ((v & 0x2000000) === 0) {
        c += 1;
    }
    return c;
}

let _10_pow_log10_of_digMax = double_pow(10, digMax_log10);

assert(digBase_log2 <= 30);
assert((digBase & (digBase - 1)) === 0);
function double_intPartLeastSignificantDigit(n) {
    return n & digMax;
}

function doubleArr_hasOnlyZeroes(doubleArr: number[], end: number): boolean {
    for (let i = 0; i < end; ++i) {
        if (doubleArr[i] !== 0) {
            return false;
        }
    }
    return true;
}

function doubleArr_copy(doubleArr_src: number[], doubleArr_dst: number[], start: number, end: number): void {
    for (let i: number = start; i < end; i++) {
        doubleArr_dst[i] = doubleArr_src[i];
    }
}

function doubleArr_getLengthOfLongestCommonPrefix(doubleArr1: number[], doubleArr2: number[]): number {
    let i = doubleArr1.length;
    assert(doubleArr2.length === i);
    assert(0 < i);
    while (doubleArr1[--i] === doubleArr2[i]) {
        if (i === 0) {
            return 0;
        }
    }
    return i + 1;
}

function digArr_fromAbsOfLargeIntDouble(largeIntDouble: number): number[] {
    if (largeIntDouble < 0) {
        largeIntDouble = -largeIntDouble;
    }
    let dbl = largeIntDouble;
    let largeIntDouble_ieee754Exp = doubleUtil.getExponent(largeIntDouble);
    let largeIntDouble_asInteger_noBits = largeIntDouble_ieee754Exp + 1;
    let digArr_len = double_ceil(largeIntDouble_asInteger_noBits / digBase_log2);
    let digArr = new Array(digArr_len);
    let largeIntDouble_asInteger_noTrailingZeroBits = double_max(0, largeIntDouble_asInteger_noBits - (doubleUtil_mantissaSize_base2 + 1));
    let largeIntDouble_asInteger_noTrailingZeroDigits = double_floor(largeIntDouble_asInteger_noTrailingZeroBits / digBase_log2);
    let i = 0;
    for (; i < largeIntDouble_asInteger_noTrailingZeroDigits; ++i) {
        digArr[i] = 0;
    }
    dbl = dbl * double_pow(2, -largeIntDouble_asInteger_noTrailingZeroDigits * digBase_log2);
    while (true) {
        digArr[i] = double_intPartLeastSignificantDigit(dbl);
        dbl = dbl * digBase_reciprocal;
        if (dbl < 1) {
            break;
        }
        assert(++i < digArr_len);
    }
    return digArr;
}

let String_fromCharCode = String.fromCharCode;

let __Integer: (a: number[], n: number) => void;

export class Integer {

    public static DIGIT_BASE_LOG2: number = 26;

    private static validateNormalize(dblOrInt: number | Integer): number | Integer {
        if (isIntegralDouble(dblOrInt)) {
            if (-digBase < dblOrInt && dblOrInt < digBase) {
                return dblOrInt;
            }
            return new __Integer(
                digArr_fromAbsOfLargeIntDouble(<number>dblOrInt),
                <number>dblOrInt < 0 ? -1 : 1);
        }
        if (dblOrInt instanceof Integer) {
            if (dblOrInt._a === null) {
                return dblOrInt._n;
            }
            return dblOrInt;
        }
        throw new TypeError();
    }

    private _n: number;
    private _a: number[];

    constructor(dblOrInt: number | Integer = 0) {
        // Same as assign, but inlined for speed.
        if (isIntegralDouble(dblOrInt)) {
            if (-digMax <= dblOrInt && dblOrInt <= digMax) {
                this._n = <number>dblOrInt;
                this._a = null;
                return;
            }
            this._a = digArr_fromAbsOfLargeIntDouble(<number>dblOrInt);
            this._n = dblOrInt < 0 ? -1 : 1;
            return;
        }
        if (dblOrInt instanceof Integer) {
            this._a = (<Integer>dblOrInt)._a.slice(0);
            this._n = (<Integer>dblOrInt)._n;
            return;
        }
        throw new TypeError();
    }

    public static add(dblOrInt1: number | Integer, dblOrInt2: number | Integer): Integer {
        let digOrLargeInt = Integer.validateNormalize(dblOrInt1);
        let sum: Integer;
        if (typeof digOrLargeInt === "number") {
            sum = new __Integer(null, digOrLargeInt);
        } else {
            sum._a = digOrLargeInt._a.slice(0);
            sum._n = digOrLargeInt._n;
        }
        sum.addAssign(dblOrInt2);
        return sum;
    }

    public addAssign(dblOrInt: number | Integer): Integer {
        let digOrLargeInt = Integer.validateNormalize(dblOrInt);
        if (typeof digOrLargeInt === "number") {
            if (this._a === null) {
                this._addAssign_ss(digOrLargeInt);
                return this;
            }
            this._addAssign_ld(digOrLargeInt);
            return this;
        }
        let largeInt = <Integer>digOrLargeInt;
        if (this._a === null) {
            let t = this._n;
            this._assign_largeInt(largeInt);
            this._addAssign_ld(t);
            return this;
        }
        if ((this._n < 0) === (largeInt._n < 0)) {
            this._addAssign_llm(largeInt);
        } else {
            this._subtractAssign_ll(largeInt);
        }
        return this;
    }

    private _addAssign_llm(largeInt: Integer): void {
        let digArr_this = this._a;
        let digArr_largeInt = largeInt._a;
        let digCount_this_old = digArr_this.length;
        for (let i = digCount_this_old, digCount_largeInt = digArr_largeInt.length; i < digCount_largeInt; ++i) {
            digArr_this[i] = digArr_largeInt[i];
        }
        let carry = 0;
        for (let i = 0; i < digCount_this_old; ++i) {
            let digBig = carry + digArr_this[i] + digArr_largeInt[i];
            digArr_this[i] = double_intPartLeastSignificantDigit(digBig);
            // double_floor is not needed here but hopefully this will make the interpreter's task of optimizing easier.
            carry = double_floor(digBig * digBase_reciprocal);
        }
        if (0 < carry) {
            this._applyCarry(digCount_this_old);
        }
    }

    private _addAssign_ld(dig: number): void {
        if ((this._n < 0) === (dig < 0)) {
            dig = double_abs(dig) + this._a[0];
            if (dig <= digMax) {
                this._a[0] = dig;
                return;
            }
            this._a[0] = double_intPartLeastSignificantDigit(dig);
            this._applyCarry(1);
            return;
        }
        dig = this._a[0] - double_abs(dig);
        if (0 <= dig) {
            this._a[0] = dig;
            return;
        }
        this._a[0] = dig + digBase;
        this._applyBorrow(1);
        this._trimMostSignificantZeroDigits();
    }

    private _addAssign_ss(dig: number): void {
        let t = this._n + dig;
        if (-digBase < t && t < digBase) {
            this._n = t;
            return;
        }
        if (t < 0) {
            this._n = -1;
            t = -t;
        } else {
            this._n = 1;
        }
        this._a = [double_intPartLeastSignificantDigit(t), 1];
    }

    private _applyCarry(start: number): void {
        let i = start;
        let digArr_this = this._a;
        while (i < digArr_this.length) {
            if (++digArr_this[i] < digBase) {
                return;
            }
            digArr_this[i] = 0;
            if (++i === i) {
                throw new Error();
            }
        }
        digArr_this[i] = 1;
    }

    private _applyBorrow(start: number): void {
        let i = start;
        let digArr_this = this._a;
        assert(i < digArr_this.length);
        // Assume we can borrow, otherwise this number would not have had more digits.
        while (--digArr_this[i] < 0) {
            digArr_this[i] = digMax;
            assert(++i < digArr_this.length);
        }
    }

    public assign(dblOrInt: number | Integer): Integer {
        if (isIntegralDouble(dblOrInt)) {
            if (-digMax <= dblOrInt && dblOrInt <= digMax) {
                this._n = <number>dblOrInt;
                this._a = null;
                return this;
            }
            this._a = digArr_fromAbsOfLargeIntDouble(<number>dblOrInt);
            this._n = dblOrInt < 0 ? -1 : 1;
            return this;
        }
        if (dblOrInt instanceof Integer) {
            this._assign_largeInt(<Integer>dblOrInt);
            return this;
        }
        throw new TypeError();
    }

    private _assign_largeInt(largeInt: Integer): void {
        this._n = largeInt._n;
        this._a = largeInt._a.slice(0);
    }

    public compareTo(dblOrInt: number | Integer): number {
        let digOrLargeInt = Integer.validateNormalize(dblOrInt);
        let digArr_this = this._a;
        if (typeof digOrLargeInt === "number") {
            if (digArr_this === null) {
                return this._n - digOrLargeInt;
            }
            // -- > -1
            // -+ > -1
            // +- > 1
            // ++ > 1
            return this._n;
        }
        let digArr_largeInt: number[];
        if (digArr_this === null || digArr_this.length < (digArr_largeInt = (<Integer>digOrLargeInt)._a).length) {
            // -- > 1
            // -+ > -1
            // +- > 1
            // ++ > -1
            return -(<Integer>digOrLargeInt)._n;
        }
        if (digArr_largeInt.length < digArr_this.length) {
            return this._n;
        }
        let indexOfMostSignificantDifferentDigit_plusOne = doubleArr_getLengthOfLongestCommonPrefix(digArr_this, digArr_largeInt);
        if (indexOfMostSignificantDifferentDigit_plusOne === 0) {
            return 0;
        }
        let indexOfMostSignificantDifferentDigit = indexOfMostSignificantDifferentDigit_plusOne - 1;
        return digArr_this[indexOfMostSignificantDifferentDigit] - digArr_largeInt[indexOfMostSignificantDifferentDigit];
    }

    public static divide(dblOrInt_dividend: number | Integer, dblOrInt_divisor: number | Integer): Integer {
        let digOrLargeIntNum = Integer.validateNormalize(dblOrInt_dividend);
        let digOrLargeIntDen = Integer.validateNormalize(dblOrInt_divisor);
        if (digOrLargeIntDen === 0) {
            throw new Error();
        }
        if (typeof digOrLargeIntNum === "number") {

        } else {

        }
        throw new Error('not impl');
    }

    public static divRem(dblOrInt_dividend: number | Integer, dblOrInt_divisor: number | Integer, int_quotient: Integer, int_remainder: Integer): void {
        let digOrLargeIntNum = Integer.validateNormalize(dblOrInt_dividend);
        let digOrLargeIntDen = Integer.validateNormalize(dblOrInt_divisor);
        if (int_quotient == null || int_remainder == null) {
            // Invalid arguments
            throw new TypeError();
        }
        if (int_quotient === int_remainder) {
            // Invalid arguments
            throw new Error();
        }
        if (digOrLargeIntDen === 0) {
            // Division by zero.
            throw new Error();
        }
        if (typeof digOrLargeIntNum === "number") {
            if (typeof digOrLargeIntDen === "number") {
                let quotient_dig = double_roundToZero(digOrLargeIntNum / digOrLargeIntDen);
                int_remainder._a = null;
                int_remainder._n = digOrLargeIntNum - digOrLargeIntDen * quotient_dig;
                int_quotient._a = null;
                int_quotient._n = quotient_dig;
                return;
            }
            if (digOrLargeIntDen === int_quotient || digOrLargeIntDen === int_remainder) {
                // Invalid arguments
                throw new Error();
            }
            int_remainder._a = null;
            int_remainder._n = digOrLargeIntNum;
            int_quotient._n = 0;
            int_quotient._a = null;
            return;
        }
        if (digOrLargeIntNum === int_quotient || digOrLargeIntNum === int_remainder) {
            // Invalid arguments.
            throw new Error();
        }
        if (typeof digOrLargeIntDen === "number") {
            Integer._divRem_ld(<Integer>digOrLargeIntNum, digOrLargeIntDen, int_quotient, int_remainder);
            return;
        }
        Integer._divRem_ll(<Integer>digOrLargeIntNum, <Integer>digOrLargeIntDen, int_quotient, int_remainder);
    }

    private static _divRem_ll(largeInt_num: Integer, largeInt_den: Integer, quo: Integer, rem: Integer): void {
        let digArr_num = largeInt_num._a;
        let digCount_num = digArr_num.length;
        let digArr_curRem: number[] = rem._a;
        if (digArr_curRem === null || digArr_curRem.length < digCount_num) {
            digArr_curRem = digArr_num.slice(0);
        } else {
            doubleArr_copy(digArr_num, digArr_curRem, 0, digCount_num);
        }
        rem._a = digArr_curRem;
        rem._n = 1;
        let digArr_den = largeInt_den._a;
        let digCount_den = digArr_den.length;
        if (digCount_num < digCount_den) {
            digArr_curRem.length = digCount_num;
            quo._a = null;
            quo._n = 0;
            return;
        }
        let digCountDiff = digCount_num - digCount_den;
        let digCount_quo = digCountDiff;
        for (let i = digCount_num; ;) {
            i -= 1;
            if (i < digCountDiff) {
                digCount_quo += 1;
                break;
            }
            if (digArr_den[i - digCountDiff] != digArr_num[i]) {
                if (digArr_den[i - digCountDiff] < digArr_num[i]) {
                    digCount_quo += 1;
                }
                break;
            }
        }
        if (digCount_quo === 0) {
            digArr_curRem.length = digCount_num;
            quo._n = 0;
            quo._a = null;
            return;
        }
        quo._n = largeInt_num._n * largeInt_den._n;
        let digNorm_denMostSig1 = digArr_den[digCount_den - 1];
        let digNorm_denMostSig2 = digArr_den[digCount_den - 2];
        let normLShift = dig_noMostSignificantZeroBits(digNorm_denMostSig1);
        let normRShift = digBase_log2 - normLShift;
        if (0 < normLShift) {
            digNorm_denMostSig1 = double_intPartLeastSignificantDigit(digNorm_denMostSig1 << normLShift) | (digNorm_denMostSig2 >>> normRShift);
            digNorm_denMostSig2 = double_intPartLeastSignificantDigit(digNorm_denMostSig2 << normLShift);
            if (2 < digCount_den) {
                digNorm_denMostSig2 |= digArr_den[digCount_den - 3] >>> normRShift;
            }
        }
        // The most significant digit of digNorm_denMostSig1 is set.
        // 0 <= digCount_num - digCount_quo + digCount_den <= 1
        let digCount_curRem = digCount_num;
        let digArr_quo: number[];
        if (1 < digCount_quo) {
            digArr_quo = quo._a;
            if (digArr_quo === null) {
                digArr_quo = new Array(digCount_quo);
            } else {
                digArr_quo.length = digCount_quo;
            }
        } else {
            digArr_quo = readOnlyArr_len1;
        }
        for (let i = digCount_quo; -1 < --i; ) {
            let dig_num1 = i + digCount_den < digCount_num
                ? digArr_curRem[i + digCount_den]
                : 0;
            // dig_num1 is at most digArr_den[digCount_den - 1]
            let digNormBig_num = dig_num1 * digBase + digArr_curRem[i + digCount_den - 1];
            let digNorm_digNormBigNumeratorNext = digArr_curRem[i + digCount_den - 2];
            if (0 < normLShift) {
                digNormBig_num = digNormBig_num * readOnlyArr_pow2[normLShift] + (digNorm_digNormBigNumeratorNext >>> normRShift);
                digNorm_digNormBigNumeratorNext = double_intPartLeastSignificantDigit(digNorm_digNormBigNumeratorNext << normLShift);
                if (2 < i + digCount_den) {
                    digNorm_digNormBigNumeratorNext |= digArr_den[i + digCount_den - 3] >>> normRShift;
                }
            }
            let bigDig_quo = double_floor(digNormBig_num / digNorm_denMostSig1);
            let bigDig_rem = digNormBig_num - digNorm_denMostSig1 * bigDig_quo;
            // bigDig_quo is at most two higher than digMax
            if (bigDig_quo > digMax) {
                bigDig_rem += digNorm_denMostSig1 * (bigDig_quo - digMax);
                bigDig_quo = digMax;
            }
            while (bigDig_rem <= digMax &&
                bigDig_rem * digBase + digNorm_digNormBigNumeratorNext < bigDig_quo * digNorm_denMostSig2) {
                bigDig_quo -= 1;
                bigDig_rem += digNorm_denMostSig1;
            }
            // bigDig_quo is now at most one too large and fits in one digit.
            if (0 < bigDig_quo) {
                let borrow = 0;
                for (let j = 0; ; ) {
                    borrow += digArr_den[j] * bigDig_quo;
                    let dig1 = double_intPartLeastSignificantDigit(borrow);
                    borrow = double_floor(borrow * digBase_reciprocal);
                    let dig2 = digArr_curRem[i + j] - dig1;
                    if (dig2 < 0) {
                        borrow += 1;
                        dig2 += digBase;
                    }
                    digArr_curRem[i + j] = dig2;
                    if (++j === digCount_den) break;
                }
                assert(dig_num1 === borrow || dig_num1 === borrow - 1);
                if (dig_num1 < borrow) {
                    let carry = 0;
                    for (let j = 0; ; ) {
                        carry += digArr_den[j] + digArr_curRem[i + j];
                        digArr_curRem[i + j] = double_intPartLeastSignificantDigit(carry);
                        carry >>= digBase_log2;
                        if (++j === digCount_den) break;
                    }
                    // Carry is at most one.
                    bigDig_quo -= 1;
                }
                digCount_curRem -= 1;
            }
            digArr_quo[i] = bigDig_quo;
        }
        if (1 < digCount_quo) {
            quo._a = digArr_quo;
        } else {
            quo._a = null;
            quo._n *= digArr_quo[0];
        }
        if (1 < digCount_curRem) {
            digArr_curRem.length = digCount_curRem;
        } else {
            rem._a = null;
            rem._n = digArr_curRem[0];
        }
    }

    private static _divRem_ld(largeInt_num: Integer, den: number, quo: Integer, rem: Integer): void {
        // let digArr_curRem: number[] = rem._a;
        // if (digArr_curRem === null || digArr_curRem.length < digCount_num) {
        //     digArr_curRem = digArr_num.slice(0);
        // } else {
        //     doubleArr_copy(digArr_num, digArr_curRem, 0, digCount_num);
        // }
        // rem._a = digArr_curRem;
        // rem._n = 1;


        throw new Error('not impl');
    }

    public multiplyAssign(dblOrInt: number | Integer): Integer {
        throw new Error('not impl');
    }

    public static parse(s: string): Integer {
        if (!/^[-\+]?[0-9]+$/.test(s)) {
            throw new SyntaxError();
        }
        let n = Number(s);
        if (String(n) === s) {
            return new Integer(n);
        }
        let i = 0;
        let cp1 = s.charCodeAt(0);
        if (cp1 === 0x2D || cp1 === 0x2B) {
            i += 1;
        }
        let s_len = s.length;
        let int = new Integer();
        while (s.charCodeAt(i) === 0x30) {
            if (++i === s_len) break;
        }
        for (; i < s_len; i++) {
            int.multiplyAssign(10);
            let dig = s.charCodeAt(i) - 0x30;
            if (dig != 0) {
                int.addAssign(10);
            }
        }
        if (cp1 === 0x2D) {
            int = Integer.subtract(0, int);
        }
        return int;
    }

    public static subtract(dblOrInt1: number | Integer, dblOrInt2: number | Integer): Integer {
        let digOrLargeInt1 = Integer.validateNormalize(dblOrInt1);
        let sum: Integer;
        if (typeof digOrLargeInt1 === "number") {
            sum = new __Integer(null, digOrLargeInt1);
        } else {
            sum = new __Integer(digOrLargeInt1._a.slice(0), digOrLargeInt1._n);
        }
        sum.subtractAssign(dblOrInt2);
        return sum;
    }

    public subtractAssign(dblOrInt: number | Integer): Integer {
        let digOrLargeInt = Integer.validateNormalize(dblOrInt);
        if (typeof digOrLargeInt === "number") {
            if (this._a === null) {
                this._addAssign_ss(-digOrLargeInt);
                return this;
            }
            this._addAssign_ld(-digOrLargeInt);
            return this;
        }
        let largeInt = <Integer>digOrLargeInt;
        if (this._a === null) {
            var t = this._n;
            this._assign_largeInt(largeInt);
            this._addAssign_ld(-t);
            this._n = -this._n;
            return this;
        }
        if ((this._n < 0) === (largeInt._n < 0)) {
            this._subtractAssign_ll(largeInt);
        } else {
            this._addAssign_llm(largeInt);
        }
        return this;
    }

    public _subtractAssign_ll(largeInt: Integer): void {
        let digArr_this = this._a;
        let digArr_largeInt = largeInt._a;
        let digCount_this_old = digArr_this.length;
        let digCount_largeInt = digArr_largeInt.length;
        let borrow;
        if (digCount_largeInt < digCount_this_old) {
            borrow = this._subtractAssign_llm(digArr_largeInt, digCount_largeInt);
            if (borrow === 0) {
                return;
            }
            this._applyBorrow(digCount_largeInt);
        } else if (digCount_this_old < digCount_largeInt) {
            doubleArr_copy(digArr_largeInt, digArr_this, digCount_this_old, digCount_largeInt);
            borrow = this._subtractAssign_llm_rev(digArr_largeInt, digCount_this_old);
            if (borrow === 0) {
                return;
            }
            this._applyBorrow(digCount_this_old);
        } else {
            let digCount_this_new = doubleArr_getLengthOfLongestCommonPrefix(digArr_this, digArr_largeInt);
            if (digCount_this_new <= 1) {
                this._n = digArr_this[0] - digArr_largeInt[0];
                this._a = null;
                return;
            }
            digArr_this.length = digCount_this_new;
            if (digArr_this[digCount_this_new - 1] < digArr_largeInt[digCount_this_new - 1]) {
                borrow = this._subtractAssign_llm_rev(digArr_largeInt, digCount_this_new);
            } else {
                borrow = this._subtractAssign_llm(digArr_largeInt, digCount_this_new);
            }
            assert(borrow === 0);
            return;
        }
        this._trimMostSignificantZeroDigits();
    }

    public _subtractAssign_llm(digArr_largeInt: number[], n: number): number {
        var digArr_this = this._a;
        var i = 0;
        var borrow = 0;
        for (; i < n; ++i) {
            var t = digArr_this[i] - digArr_largeInt[i] - borrow;
            if (t < 0) {
                t += digBase;
                borrow = 1;
            } else {
                borrow = 0;
            }
            digArr_this[i] = t;
        }
        return borrow;
    }

    public _subtractAssign_llm_rev(digArr_largeInt: number[], n: number): number {
        var digArr_this = this._a;
        var i = 0;
        var borrow = 0;
        for (; i < n; ++i) {
            var t = digArr_largeInt[i] - digArr_this[i] - borrow;
            if (t < 0) {
                t += digBase;
                borrow = 1;
            } else {
                borrow = 0;
            }
            digArr_this[i] = t;
        }
        this._n = -this._n;
        return borrow;
    }

    public _trimMostSignificantZeroDigits(): void {
        // Assume this is large.
        let digArr_this = this._a;
        let i = digArr_this.length - 1;
        if (digArr_this[i] !== 0) {
            return;
        }
        // Trim by at least one.
        while (digArr_this[i - 1] === 0) {
            if (--i === 0) {
                this._n *= digArr_this[0];
                this._a = null;
                return;
            }
        }
        digArr_this.length = i;
    }

    public toNumber(roundingMode: RoundingMode = RoundingMode.TOWARDS_ZERO): number {
        assert(digBase_log2 === 26);
        let digArr_this = this._a;
        if (digArr_this === null) {
            return this._n;
        }
        let i = digArr_this.length;
        let noBits_mostSigDig_leadingZeros = dig_noMostSignificantZeroBits(digArr_this[i - 1]);
        let noBits = i * digBase_log2 - noBits_mostSigDig_leadingZeros;
        let exp = noBits - 1;
        assert(0 <= exp);
        if (doubleUtil_expMaxMinusMantNoBits <= exp) {
            return this._n * double_posInf;
        }
        assert(this._n !== 0);
        let mant = digArr_this[--i] & ((1 << (digBase_log2 - noBits_mostSigDig_leadingZeros - 1)) - 1);
        let mantNoBitsRem = doubleUtil_mantissaSize_base2 - (digBase_log2 - noBits_mostSigDig_leadingZeros - 1);

        mant = mant * digBase + digArr_this[--i];
        mantNoBitsRem -= digBase_log2;

        mant = mant * double_pow(2, mantNoBitsRem);
        if (0 < i && mantNoBitsRem === digBase_log2) {
            mant += digArr_this[--i];
            mantNoBitsRem = 0;
        }
        if (i === 0) {
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        assert(mantNoBitsRem < digBase_log2);
        let firstNotFullyReprDig_noUnreprBits = (digBase_log2 - mantNoBitsRem);
        mant += digArr_this[--i] >>> firstNotFullyReprDig_noUnreprBits;
        mantNoBitsRem = 0;
        void mantNoBitsRem;
        let roundingFlag: boolean;
        switch (roundingMode) {
            case RoundingMode.AWAY_FROM_ZERO:
                roundingFlag = true;
                break;
            case RoundingMode.TOWARDS_ZERO:
                roundingFlag = false;
                break;
        }
        if (roundingFlag !== undefined) {
            if (roundingFlag === true) {
                return doubleUtil_incMantAndCreate(exp, mant, this._n < 0);
            }
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        var firstNotFullyReprDig_unreprPart = (digArr_this[i] & ((1 << firstNotFullyReprDig_noUnreprBits) - 1));
        var nonFirstNotFullyReprDigs_areAllZero = doubleArr_hasOnlyZeroes(digArr_this, i);
        var requiresRounding = firstNotFullyReprDig_unreprPart !== 0 || !nonFirstNotFullyReprDigs_areAllZero;
        if (roundingMode == null && requiresRounding) {
            // Rounding mode is explicitly equal (==) to null and this integer is not representable by a number.
            return double_notANumber;
        }
        if (!requiresRounding) {
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        var mpInfo = firstNotFullyReprDig_unreprPart - (1 << (firstNotFullyReprDig_noUnreprBits - 1));
        if (mpInfo === 0 && !nonFirstNotFullyReprDigs_areAllZero) {
            mpInfo = this._n < 0 ? -1 : 1;
        }
        if (mpInfo !== 0) {
            if (0 < mpInfo) {
                // mag above midpoint, round mag awayFromZero
                roundingFlag = 0 < this._n;
            } else {
                // mag below midpoint, round mag towardsZero
                roundingFlag = this._n < 0;
            }
        } else {
            switch (roundingMode) {
                case RoundingMode.MP_AWAY_FROM_ZERO:
                    roundingFlag = true;
                    break;
                case RoundingMode.MP_TOWARDS_ZERO:
                    roundingFlag = false;
                    break;
                case RoundingMode.BANKERS:
                    roundingFlag = (mant & 1) !== 0;
                    break;
            }
        }
        assert(typeof roundingFlag === "boolean");
        if (roundingFlag) {
            return doubleUtil_incMantAndCreate(exp, mant, this._n < 0);
        }
        return doubleUtil.create(exp, mant, this._n < 0);
    }

    public toString(): string {
        let digArr_this = this._a;
        if (digArr_this === null) {
            return this._n + "";
        }
        let va = [];
        let va_len = 0;
        let i = digArr_this.length;
        let t1, t2, j;
        while (0 <= --i) {
            t1 = digArr_this[i];
            for (j = 0; j < va_len; ++j) {
                t2 = va[j] * digBase + t1;
                va[j] = t2 % _10_pow_log10_of_digMax;
                t1 = double_floor(t2 / _10_pow_log10_of_digMax);
            }
            if (0 < t1) {
                va[va_len++] = t1 % _10_pow_log10_of_digMax;
                t1 = double_floor(t1 / _10_pow_log10_of_digMax);
                if (0 < t1) {
                    va[va_len++] = t1;
                }
            }
        }
        let s = "";
        for (i = 0; i < va_len - 1; ++i) {
            t1 = va[i];
            for (j = 0; j < digMax_log10; ++j) {
                s = String_fromCharCode(48 + t1 % 10) + s;
                t1 = double_floor(t1 / 10);
            }
        }
        for (t1 = va[va_len - 1]; 1 <= t1; t1 = double_floor(t1 / 10)) {
            s = String_fromCharCode(48 + t1 % 10) + s;
        }
        if (this._n < 0) {
            s = "-" + s;
        }
        return s;
    }

    public valueOf(): number {
        return this.toNumber(RoundingMode.BANKERS);
    }
}
__Integer = function __Integer(a: number[], n: number): void {
    this._a = a;
    this._n = n;
};
__Integer.prototype = Integer.prototype;