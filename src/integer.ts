import {assert, isIntegralDouble, RoundingMode, double_log10, double_roundToZero} from "./base";
import { DoubleUtilities } from "./ieee754Utilities";
let pow = Math.pow;
let ceil = Math.ceil;
let floor = Math.floor;
let max = Math.max;
let abs = Math.abs;
let doubleUtil = DoubleUtilities.getInstance();
let doubleUtil_mantissaSize_base2 = doubleUtil.getMantissaSize_base2();
let doubleUtil_2PowMantNoBits = pow(2, doubleUtil_mantissaSize_base2);
let doubleUtil_expMaxMinusMantNoBits = doubleUtil.getExponentMax() - doubleUtil_mantissaSize_base2;
function doubleUtil_incMantAndCreate(exp, mant, isNegative) {
    mant += 1;
    if (doubleUtil_2PowMantNoBits <= mant) {
        mant = mant * 0.5;
        exp += 1;
        if (doubleUtil_expMaxMinusMantNoBits <= exp) {
            return isNegative ? -1 / 0 : 1 / 0;
        }
    }
    return doubleUtil.create(exp, mant, isNegative);
}

let digBase_log2 = 26;
let digBase = pow(2, digBase_log2);
let digBase_reciprocal = pow(2, -digBase_log2);
let digMax = digBase - 1;
let digMaxLog10 = floor(double_log10(digMax));

assert(digBase_log2 <= 30);
assert((digBase & (digBase - 1)) === 0);
function dig_noMostSignificantZeroBits(v) {
    assert(isIntegralDouble(v));
    assert(v !== 0);
    let c = 0;
    if ((v & 0x3FF0000) === 0) {
        c += 10;
        v <<= 10;
    }
    if ((v & 0x3FC0000) === 0) {
        c += 8;
        v <<= 8;
    }
    if ((v & 0x3C00000) === 0) {
        c += 4;
        v <<= 4;
    }
    if ((v & 0x3000000) === 0) {
        c += 2;
        v <<= 2;
    }
    if ((v & 0x1000000) === 0) {
        c += 1;
    }
    return c;
}

let _10_pow_digMaxLog10 = pow(10, digMaxLog10);

assert(digBase_log2 <= 30);
assert((digBase & (digBase - 1)) === 0);
function num_intPartLeastSignificantDigit(n) {
    return n & digMax;
}

let createUninitializedInteger: () => Integer;

function array_areAllElementsZero(a: number[], n: number): boolean {
    for (let i = 0; i < n; ++i) {
        if (a[i] !== 0) {
            return false;
        }
    }
    return true;
}

function array_copy(srca: number[], dsta: number[], i: number, end: number): void {
    do {
        dsta[i] = srca[i];
    } while (++i < end);
}

function getDiffLen(a1: number[], a2: number[]): number {
    let i = a1.length;
    assert(a2.length === i);
    assert(0 < i);
    while (a1[--i] === a2[i]) {
        if (i === 0) {
            return 0;
        }
    }
    return i + 1;
}

let Object_getPrototypeOf = Object.getPrototypeOf;
let String_fromCharCode = String.fromCharCode;
let Integer_prototype;

export class Integer {

    private static validateNormalize(x: number | Integer): number | Integer {
        if (isIntegralDouble(x)) {
            if (-digBase < x && x < digBase) {
                return x;
            }
            let int = createUninitializedInteger();
            int._assign_numBig(<number>x);
            return int;
        }
        if (x instanceof Integer) {
            if (x._a === null) {
                return x._n;
            }
            return x;
        }
        throw new TypeError();
    }

    private _n: number;
    private _a: number[];

    constructor(numberOrInteger: number | Integer = 0) {
        this.assign(numberOrInteger);
    }

    public static add(numberOrInteger1: number | Integer, numberOrInteger2: number | Integer): Integer {
        let doi1 = Integer.validateNormalize(numberOrInteger1);
        let sum = createUninitializedInteger();
        if (typeof doi1 === "number") {
            sum._a = null;
            sum._n = doi1;
        } else {
            sum._a = doi1._a.slice(0);
            sum._n = doi1._n;
        }
        sum.addAssign(numberOrInteger2);
        return sum;
    }

    public addAssign(numberOrInteger: number | Integer): Integer {
        let digitOrInteger = Integer.validateNormalize(numberOrInteger);
        if (typeof digitOrInteger === "number") {
            if (this._a === null) {
                this._addAssign_ss(digitOrInteger);
                return this;
            }
            this._addAssign_bs(digitOrInteger);
            return this;
        }
        let integer = <Integer>digitOrInteger;
        if (this._a === null) {
            let t = this._n;
            this._assign_b(integer);
            this._addAssign_bs(t);
            return this;
        }
        if ((this._n < 0) === (integer._n < 0)) {
            this._addAssign_bbm(integer);
        } else {
            this._subtractAssign_bb(integer);
        }
        return this;
    }

    public _addAssign_bbm(integer: Integer): void {
        var a1 = this._a;
        var a2 = integer._a;
        var a1_len_old = a1.length;
        var i, t;
        for (i = a1_len_old, t = a2.length; i < t; ++i) {
            a1[i] = a2[i];
        }
        for (i = 0, t = 0; i < a1_len_old; ++i) {
            t += a1[i] + a2[i];
            a1[i] = num_intPartLeastSignificantDigit(t);
            t *= digBase_reciprocal;
        }
        if (1 <= t) {
            this._applyCarry(a1_len_old);
        }
    }

    public _addAssign_bs(digit: number): void {
        if ((this._n < 0) === (digit < 0)) {
            digit = abs(digit) + this._a[0];
            if (digit <= digMax) {
                this._a[0] = digit;
                return;
            }
            this._a[0] = num_intPartLeastSignificantDigit(digit);
            this._applyCarry(1);
            return;
        }
        digit = this._a[0] - abs(digit);
        if (0 <= digit) {
            this._a[0] = digit;
            return;
        }
        this._a[0] = digit + digBase;
        this._applyBorrow(1);
        this._trimMostSignificantZeroDigits();
    }

    public _addAssign_ss(digit: number): void {
        digit = this._n + digit;
        if (-digBase < digit && digit < digBase) {
            this._n = digit;
            return;
        }
        if (digit < 0) {
            this._n = -1;
            digit = -digit;
        } else {
            this._n = 1;
        }
        this._a = [num_intPartLeastSignificantDigit(digit), 1];
    }

    public _applyCarry(i: number): void {
        while (i < this._a.length) {
            if (++this._a[i] < digBase) {
                return;
            }
            this._a[i] = 0;
            if (++i === i) {
                throw new Error();
            }
        }
        this._a[i] = 1;
    }

    public _applyBorrow(i: number): void {
        assert(i < this._a.length);
        // Assume we can borrow, otherwise this number would not have had more digits.
        while (--this._a[i] < 0) {
            this._a[i] = digMax;
            assert(++i < this._a.length);
        }
    }

    public assign(numberOrInteger: number | Integer): Integer {
        if (isIntegralDouble(numberOrInteger)) {
            if (-digMax <= numberOrInteger && numberOrInteger <= digMax) {
                this._n = <number>numberOrInteger;
                this._a = null;
                return this;
            }
            this._assign_numBig(<number>numberOrInteger);
            return this;
        }
        if (!(numberOrInteger instanceof Integer)) {
            throw new Error();
        }
        this._assign_b(<Integer>numberOrInteger);
        return this;
    }

    public _assign_b(integer: Integer): void {
        this._n = integer._n;
        this._a = integer._a.slice(0);
    }

    // v is a value larger than 2^26-1
    public _assign_numBig(v: number): void {
        var v_ieee754Exp = doubleUtil.getExponent(v);
        var v_noBits = v_ieee754Exp + 1;
        var v_noDigits = ceil(v_noBits / digBase_log2);
        if (v < 0) {
            this._n = -1;
            v = -v;
        } else {
            this._n = 1;
        }
        this._a = new Array(v_noDigits);
        var v_minNoLeastSignificantZeroBits = max(0, v_noBits - (doubleUtil_mantissaSize_base2 + 1));
        var v_minNoLeastSignificantZeroDigits = floor(v_minNoLeastSignificantZeroBits / digBase_log2);
        var i = 0;
        for (; i < v_minNoLeastSignificantZeroDigits; ++i) {
            this._a[i] = 0;
        }
        v = v * pow(2, -v_minNoLeastSignificantZeroDigits * digBase_log2);
        while (true) {
            this._a[i] = num_intPartLeastSignificantDigit(v);
            v = v * digBase_reciprocal;
            if (v < 1) {
                break;
            }
            assert(++i < v_noDigits);
        }
    }

    public compareTo(numberOrInteger: number | Integer): number {
        let digitOrInteger = Integer.validateNormalize(numberOrInteger);
        let thisa = this._a;
        if (typeof digitOrInteger === "number") {
            if (thisa === null) {
                return this._n - digitOrInteger;
            }
            // -- > -1
            // -+ > -1
            // +- > 1
            // ++ > 1
            return this._n;
        }
        let va: number[];
        if (thisa === null || thisa.length < (va = (<Integer>digitOrInteger)._a).length) {
            // -- > 1
            // -+ > -1
            // +- > 1
            // ++ > -1
            return -(<Integer>digitOrInteger)._n;
        }
        if (va.length < thisa.length) {
            return this._n;
        }
        var t = getDiffLen(thisa, va);
        if (t === 0) {
            return 0;
        }
        return thisa[--t] - va[t];
    }

    public static divMod(dividend: number | Integer, divisor: number | Integer, quotient: Integer, remainder: Integer): void {
        let dividend_doi = Integer.validateNormalize(dividend);
        let divisor_doi = Integer.validateNormalize(divisor);
        if (quotient == null || remainder == null) {
            throw new TypeError();
        }
        if (divisor_doi === 0) {
            throw new Error();
        }
        if (typeof dividend_doi === "number") {
            if (typeof divisor_doi === "number") {
                // Two Small numbers...
                let quotient_dig = double_roundToZero(dividend_doi / divisor_doi);
                remainder._a = null;
                remainder._n = dividend_doi - divisor_doi * quotient_dig;
                quotient._a = null;
                quotient._n = quotient_dig;
                return;
            }
            remainder._a = null;
            remainder._n = dividend_doi;
            quotient._n = 0;
            quotient._a = null;
            return;
        }
        if (typeof divisor_doi === "number") {
            Integer._divMod_bs(<Integer>dividend_doi, divisor_doi, quotient, remainder);
            return;
        }
        // TODO handle quotient === dividend || quotient === divisor
        // TODO handle remainder === dividend || remainder === divisor
        // TODO consider handling dividend === divisor

        Integer._divMod_bb(<Integer>dividend_doi, <Integer>divisor_doi, quotient, remainder);
    }

    private static _divMod_bb(dividend: Integer, divisor: Integer, quotient: Integer, rem: Integer): void {
        let currem_a = dividend._a.slice(0);
        rem._a = currem_a;
        rem._n = 1;
        let currem_n = currem_a.length;
        let den_a = divisor._a;
        let den_n = den_a.length;
        if (currem_n < den_n) {
            quotient._a = null;
            quotient._n = 0;
            return;
        }
        let den_iLast = den_n - 1;
        quotient._n = dividend._n * divisor._n;
        let r_implicitDigitShiftL = currem_n - den_n;
        let quot_a = new Array(r_implicitDigitShiftL + 1);
        quotient._a = quot_a;
        do {
            let currem_msdigits = currem_a[den_iLast + r_implicitDigitShiftL];
            let den_dig = den_a[den_iLast];
            if (currem_msdigits < den_dig) {
                quot_a[r_implicitDigitShiftL] = 0;
                if (r_implicitDigitShiftL === 0) {
                    // The current remainder is smaller than the divisor, the current quotient digit is zero.
                    break;
                }
                r_implicitDigitShiftL -= 1;
                currem_msdigits = digBase * currem_msdigits + currem_a[den_iLast + r_implicitDigitShiftL];
            }
            let qdig = floor(currem_msdigits / den_dig);
            let qden_carry = 0;
            let currem_borrow = 0;
            let qden_dig: number;
            for (let i = 0; i < den_iLast; i++) {
                let currem_dig = currem_a[r_implicitDigitShiftL + i];
                qden_dig = den_a[i] * qdig + qden_carry;
                currem_borrow = currem_dig - currem_borrow < num_intPartLeastSignificantDigit(qden_dig) ? 1 : 0;
                qden_carry = floor(digBase_reciprocal * qden_dig);
            }
            qden_dig = den_dig * qdig + qden_carry;
            if (currem_msdigits - currem_borrow < qden_dig) {
                currem_msdigits <= 1;
                qdig -= 1;

            }
        } while (-1 < --r_implicitDigitShiftL);
    }

    private static _divMod_bs(dividend: Integer, divisor: number, quotient: Integer, remainder: Integer): void {
        let rema = dividend._a.slice(0);
        remainder._a = rema;
        remainder._n = 1;
        let divisor_isNeg = divisor < 0;
        let divisor_mag = divisor_isNeg ? -divisor : divisor;

        let iLast = rema.length;
        let quotienta = new Array(iLast);
        iLast -= 1;
        let i = iLast;
        if (divisor_mag < rema[i]) {
            let qi = floor(rema[i] / divisor_mag);
            quotienta[i] = qi;
            rema[i] -= qi * divisor_mag;
        } else {
            quotienta.length -= 1;
        }
        quotient._a = quotienta;
        for (; -1 < --i; ) {
            if (divisor_mag < rema[i]) {
                let qi = floor(rema[i] / divisor_mag);
                quotienta[i] = qi;
                rema[i] -= qi * divisor_mag;
            } else if (i < iLast) {
                // use prev digit aswell...
                Integer._divMod_bs_21(rema[i + 1], rema[i], divisor_mag);
            }
            // TODO complete
        }
        throw new Error('TODO set sign in quotient._n and uncomment following line');
        // quotient._trimMostSignificantZeroDigits();
    }

    private static _divMod_bs_21(dividendHi: number, dividendLo: number, divisor: number): number {
        // how do we do this?
        let quotient = 1;

        throw new Error('not impl');
    }

    public static parse(s: string): Integer {
        if (!/^-[0-9]+$/.test(s)) {
            throw new SyntaxError();
        }
        let n = Number(s);
        if (String(n) !== s) {
            throw new Error('not impl');
        }
        return new Integer(n);
    }

    public static subtract(numberOrInteger1: number | Integer, numberOrInteger2: number | Integer): Integer {
        let doi1 = Integer.validateNormalize(numberOrInteger1);
        let sum = createUninitializedInteger();
        if (typeof doi1 === "number") {
            sum._n = doi1;
            sum._a = null;
        } else {
            sum._a = doi1._a.slice(0);
            sum._n = doi1._n;
        }
        sum.subtractAssign(numberOrInteger2);
        return sum;
    }

    public subtractAssign(numberOrInteger: number | Integer): Integer {
        let digitOrInteger = Integer.validateNormalize(numberOrInteger);
        if (typeof digitOrInteger === "number") {
            if (this._a === null) {
                this._addAssign_ss(-digitOrInteger);
                return this;
            }
            this._addAssign_bs(-digitOrInteger);
            return this;
        }
        let integer = <Integer>digitOrInteger;
        if (this._a === null) {
            var t = this._n;
            this._assign_b(integer);
            this._addAssign_bs(-t);
            this._n = -this._n;
            return this;
        }
        if ((this._n < 0) === (integer._n < 0)) {
            this._subtractAssign_bb(integer);
        } else {
            this._addAssign_bbm(integer);
        }
        return this;
    }

    public _subtractAssign_bb(integer: Integer): void {
        var thisa = this._a;
        var va = integer._a;
        var thisa_len_old = thisa.length;
        var va_len = va.length;
        var borrow;
        if (va_len < thisa_len_old) {
            borrow = this._subtractAssign_bbm(va, va_len);
            if (borrow === 0) {
                return;
            }
            this._applyBorrow(va_len);
        } else if (thisa_len_old < va_len) {
            array_copy(va, thisa, thisa_len_old, va_len);
            borrow = this._subtractAssign_bbm_rev(va, thisa_len_old);
            if (borrow === 0) {
                return;
            }
            this._applyBorrow(thisa_len_old);
        } else {
            thisa_len_old = getDiffLen(thisa, va);
            if (thisa_len_old <= 1) {
                this._n = thisa[0] - va[0];
                this._a = null;
                return;
            }
            thisa.length = thisa_len_old;
            if (thisa[thisa_len_old - 1] < va[thisa_len_old - 1]) {
                borrow = this._subtractAssign_bbm_rev(va, thisa_len_old);
            } else {
                borrow = this._subtractAssign_bbm(va, thisa_len_old);
            }
            assert(borrow === 0);
            return;
        }
        this._trimMostSignificantZeroDigits();
    }

    public _subtractAssign_bbm(va: number[], n: number): number {
        var thisa = this._a;
        var i = 0;
        var borrow = 0;
        for (; i < n; ++i) {
            var t = thisa[i] - va[i] - borrow;
            if (t < 0) {
                t += digBase;
                borrow = 1;
            } else {
                borrow = 0;
            }
            thisa[i] = t;
        }
        return borrow;
    }

    public _subtractAssign_bbm_rev(va: number[], n: number): number {
        var thisa = this._a;
        var i = 0;
        var borrow = 0;
        for (; i < n; ++i) {
            var t = va[i] - thisa[i] - borrow;
            if (t < 0) {
                t += digBase;
                borrow = 1;
            } else {
                borrow = 0;
            }
            thisa[i] = t;
        }
        this._n = -this._n;
        return borrow;
    }

    public _trimMostSignificantZeroDigits(): void {
        // Assume 2 <= this.__a.length.
        var a = this._a;
        var i = a.length - 1;
        if (a[i] !== 0) {
            return;
        }
        // Trim by at least one.
        while (a[i - 1] === 0) {
            if (--i === 0) {
                this._n = this._n * this._a[0];
                this._a = null;
                return;
            }
        }
        a.length = i;
    }

    public toNumber(roundingMode: RoundingMode = RoundingMode.TOWARDS_ZERO): number {
        assert(digBase_log2 === 26);
        let thisa = this._a;
        if (thisa === null) {
            return this._n;
        }
        let i = thisa.length;
        let msd_mszbc = dig_noMostSignificantZeroBits(thisa[i - 1]);
        let noBits = i * digBase_log2 - msd_mszbc;
        let exp = noBits - 1;
        assert(0 <= exp);
        if (doubleUtil_expMaxMinusMantNoBits <= exp) {
            return this._n < 0 ? -1 / 0 : 1 / 0;
        }
        assert(this._n !== 0);
        let mant = thisa[--i] & ((1 << (digBase_log2 - msd_mszbc - 1)) - 1);
        let mantNoBitsRem = doubleUtil_mantissaSize_base2 - (digBase_log2 - msd_mszbc - 1);

        mant = mant * digBase + thisa[--i];
        mantNoBitsRem -= digBase_log2;

        mant = mant * pow(2, mantNoBitsRem);
        if (0 < i && mantNoBitsRem === digBase_log2) {
            mant += thisa[--i];
            mantNoBitsRem = 0;
        }
        if (i === 0) {
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        assert(mantNoBitsRem < digBase_log2);
        let firstNotFullyReprDig_noUnreprBits = (digBase_log2 - mantNoBitsRem);
        mant += thisa[--i] >>> firstNotFullyReprDig_noUnreprBits;
        mantNoBitsRem = 0;
        let shouldCeilMagWrtRM;
        switch (roundingMode) {
            case RoundingMode.AWAY_FROM_ZERO:
                shouldCeilMagWrtRM = true;
                break;
            case RoundingMode.TOWARDS_ZERO:
                shouldCeilMagWrtRM = false;
                break;
        }
        if (shouldCeilMagWrtRM !== undefined) {
            if (shouldCeilMagWrtRM === true) {
                return doubleUtil_incMantAndCreate(exp, mant, this._n < 0);
            }
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        var firstNotFullyReprDig_unreprPart = (thisa[i] & ((1 << firstNotFullyReprDig_noUnreprBits) - 1));
        var nonFirstNotFullyReprDigs_areAllZero = array_areAllElementsZero(thisa, i);
        var mustRound = firstNotFullyReprDig_unreprPart !== 0 || !nonFirstNotFullyReprDigs_areAllZero;
        if (roundingMode == null && mustRound) {
            // Rounding mode is explicitly equal (==) to null and this integer is not representable by a number.
            return 0 / 0;
        }
        if (!mustRound) {
            return doubleUtil.create(exp, mant, this._n < 0);
        }
        var mpInfo = firstNotFullyReprDig_unreprPart - (1 << (firstNotFullyReprDig_noUnreprBits - 1));
        if (mpInfo === 0 && !nonFirstNotFullyReprDigs_areAllZero) {
            mpInfo = this._n < 0 ? -1 : 1;
        }
        if (mpInfo !== 0) {
            if (0 < mpInfo) {
                // mag above midpoint, round mag awayFromZero
                shouldCeilMagWrtRM = 0 < this._n;
            } else {
                // mag below midpoint, round mag towardsZero
                shouldCeilMagWrtRM = this._n < 0;
            }
        } else {
            switch (roundingMode) {
                case RoundingMode.MP_AWAY_FROM_ZERO:
                    shouldCeilMagWrtRM = true;
                    break;
                case RoundingMode.MP_TOWARDS_ZERO:
                    shouldCeilMagWrtRM = false;
                    break;
                case RoundingMode.BANKERS:
                    shouldCeilMagWrtRM = (mant & 1) !== 0;
                    break;
            }
        }
        assert(typeof shouldCeilMagWrtRM === "boolean");
        if (shouldCeilMagWrtRM) {
            return doubleUtil_incMantAndCreate(exp, mant, this._n < 0);
        }
        return doubleUtil.create(exp, mant, this._n < 0);
    }

    public toString(): string {
        var thisa = this._a;
        if (thisa === null) {
            return this._n + "";
        }
        var va = [];
        var va_len = 0;
        var i = thisa.length;
        var t1, t2, j;
        while (0 <= --i) {
            t1 = thisa[i];
            for (j = 0; j < va_len; ++j) {
                t2 = va[j] * digBase + t1;
                va[j] = t2 % _10_pow_digMaxLog10;
                t1 = floor(t2 / _10_pow_digMaxLog10);
            }
            if (0 < t1) {
                va[va_len++] = t1 % _10_pow_digMaxLog10;
                t1 = floor(t1 / _10_pow_digMaxLog10);
                if (0 < t1) {
                    va[va_len++] = t1;
                }
            }
        }
        var s = "";
        for (i = 0; i < va_len - 1; ++i) {
            t1 = va[i];
            for (j = 0; j < digMaxLog10; ++j) {
                s = String_fromCharCode(48 + t1 % 10) + s;
                t1 = floor(t1 / 10);
            }
        }
        for (t1 = va[va_len - 1]; 1 <= t1; t1 = floor(t1 / 10)) {
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
Integer_prototype = Integer.prototype;
let Object_create = Object.create;
createUninitializedInteger = () => {
    return Object_create(Integer_prototype);
};