import { isIntegralDouble, isFiniteDouble } from "./base";

export abstract class Ieee754FloatingPointUtilities {

    private _mantNoBits: number;
    private _expNoBits: number;
    private _expBias: number;
    private _expMax: number;

    constructor(mantNoBits: number, expNoBits: number) {
        if (!isIntegralDouble(mantNoBits) || mantNoBits < 0 || 52 < mantNoBits) throw new Error();
        if (!isIntegralDouble(mantNoBits) || expNoBits < 0 || 11 < expNoBits) throw new Error();
        this._mantNoBits = mantNoBits;
        this._expNoBits = expNoBits;
        this._expBias = (1 << (this._expNoBits - 1)) - 1;
        this._expMax = (1 << this._expNoBits) - 1 - this._expBias;
    }


    public getMantissaSize_base2(): number {
        return this._mantNoBits;
    }

    public getExponentSize_base2(): number {
        return this._expNoBits;
    }

    public getExponentMin(): number {
        return -this._expBias;
    }

    public getExponentMax(): number {
        return this._expMax;
    }

    public getExponentBias(): number {
        return this._expBias;
    }

    public abstract getExponent(value): number;

    public abstract create(exponent: number, mantissa: number, isNegative: boolean);
}

let pow = Math.pow;

export class DoubleUtilities extends Ieee754FloatingPointUtilities {

    private _2PowMantNoBits: number;
    private _minNormalizedV: number;
    private _arrE: number[];
    private _arr2PowE: number[];
    private _mantMax: number;

    constructor() {
        super(52, 11);
        this._2PowMantNoBits = pow(2, this.getMantissaSize_base2());
        this._minNormalizedV = pow(2, this.getExponentMin() + 1);
        let arrE = [512, 256, 128, 64, 32, 16, 8, 4, 2, 1];
        this._arrE = arrE;
        let arrE_len = this._arrE.length;
        let arr2PowE = new Array(arrE_len);
        this._arr2PowE = arr2PowE;
        for (let i = 0; i < arrE_len; ++i) {
            arr2PowE[i] = pow(2, arrE[i]);
        }
        this._mantMax = this._2PowMantNoBits - 1;
    }

    public create(exponent: number, mantissa: number, isNegative: boolean = false): number {
        let expMin;
        let expMax;
        if (exponent < (expMin = this.getExponentMin())
            || (expMax = this.getExponentMax()) < exponent
            || !isIntegralDouble(exponent)) {
            throw new Error();
        }
        if (mantissa < 0 || this._mantMax < mantissa || !isIntegralDouble(mantissa)) {
            throw new Error();
        }
        if (typeof isNegative !== "boolean") {
            throw new TypeError();
        }
        let n;
        if (exponent === expMax) {
            if (mantissa === 0) {
                n = 1 / 0;
            } else {
                n = 0 / 0;
            }
        } else {
            n = (mantissa + (exponent !== expMin ? this._2PowMantNoBits : 0)) * pow(2, exponent - this.getMantissaSize_base2());
        }
        if (isNegative) {
            n = -n;
        }
        return n;
    }

    public getExponent(v1): number {
        if (typeof v1 !== "number") {
            throw new Error();
        }
        if (!isFinite(v1)) {
            return this.getExponentMax();
        }
        if (v1 < 0) {
            v1 = -v1;
        }
        if (v1 < this._minNormalizedV) {
            return this.getExponentMin();
        }
        var v2, i = 0, e = 0;
        var arrE = this._arrE;
        var arrE_len = arrE.length;
        var arr2PowE = this._arr2PowE;
        if (v1 < 1) {
            for (; i < arrE_len; ++i) {
                v2 = v1 * arr2PowE[i];
                if (v2 < 2) {
                    v1 = v2;
                    e -= arrE[i];
                }
            }
        } else {
            for (; i < arrE_len; ++i) {
                v2 = arr2PowE[i];
                if (v2 <= v1) {
                    v1 /= v2;
                    e += arrE[i];
                }
            }
        }
        return e;
    }

    private static instance: DoubleUtilities = new DoubleUtilities();

    public static getInstance(): DoubleUtilities {
        return DoubleUtilities.instance;
    }
}

// This operation is equivalent to floor(log2(v1)), but this implementation is guaranteed to be correct for all doubles (100% accuracy).
// Furthermore, this implementation throws an error for non-positive and non-finite v1 (for which log2 is mathematically undefined).
export function double_log2Floor(x: number): number {
    var exp, mant;
    if (!isFiniteDouble(x) || x <= 0) throw new Error();
    if (x < 2) return 0;
    exp = DoubleUtilities.getInstance().getExponent(x);
    return exp;
}