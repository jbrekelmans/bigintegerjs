var chai = require('chai');
var Integer = require('../build/integer.js').Integer;
var assert = chai.assert;

describe("number to integer to string", function() {
    it("can encode Number.MAX_VALUE", function() {
        var i = new Integer(Number.MAX_VALUE);
        var stri = i.toString();
        assert.strictEqual(stri, "179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368");
    });

    it("can encode 0", function() {
        var i = new Integer(0);
        var stri = i.toString();
        assert.strictEqual(stri, "0");
    });

    it("can encode -1", function() {
        var i = new Integer(-1);
        var stri = i.toString();

        assert.strictEqual(stri, "-1");
    });
});

describe("toNumber", function() {
    var arr = [0, -1234];
    for (var i = 0; i < 100; i++) {
        arr.push(Math.pow(2, i));
    }
    for (var i = 0; i < arr.length; i++) {
        it("should return " + arr[i], (function (num_exp) {
            return function() {
                var num_act = new Integer(num_exp).toNumber();
                assert.strictEqual(num_act, num_exp);
            };
        })(arr[i]));
    }
});

describe("parameterValidation", function() {
    it ("should successfully add two large integers that are the same", function() {
        var num1 = Math.pow(2, Integer.DIGIT_BASE_LOG2);
        var i1 = new Integer(num1 - 1);
        var i2 = Integer.add(i1, i1);
        var num2 = i2.toNumber(null);
        assert.strictEqual((num1 - 1) * 2, num2);
    });
    it ("should return zero when subtracting two large integers that are the same", function() {
        var num1 = Math.pow(2, Integer.DIGIT_BASE_LOG2);
        var i1 = new Integer(num1 - 1);
        var i2 = Integer.subtract(i1, i1);
        var c = i2.compareTo(0);
        assert.strictEqual(c, 0);
    });
});

describe("addAssign", function() {

});

describe("divRem", function() {
    describe("quotient", function() {
        var triples = [
            ["928467192823112341212341234","98123498123295123","9462230868"]
        ];
        for (var i = 0; i < triples.length; i++) {
            (function (triple) {
                it("floor(" + triple[0] + " / " + triple[1] + ") = " + triple[2], function() {
                    var dividend = Integer.parse(triple[0]);
                    var divisor = Integer.parse(triple[1]);
                    var q = new Integer();
                    var r = new Integer();
                    Integer.divRem(dividend, divisor, q, r);
                    assert.strictEqual(triple[2], q.toString());
                });
            })(triples[i]);
        }
    });
    describe("remainder for small dividend", function() {
        var triples = [
            ["-9", "2", "-1"],
            ["-1", "2", "-1"],
            ["-9", "-2", "-1"],
            ["-1", "-2", "-1"],
            ["9", "2", "1"],
            ["1", "2", "1"],
            ["9", "-2", "1"],
            ["1", "-2", "1"],
            ["-9", "200000000", "-9"],
            ["-1", "200000000", "-1"],
            ["-9", "-200000000", "-9"],
            ["-1", "-200000000", "-1"],
            ["9", "200000000", "9"],
            ["1", "200000000", "1"],
            ["9", "-200000000", "9"],
            ["1", "-200000000", "1"],
        ];
        for (var i = 0; i < triples.length; i++) {
            (function (triple) {
                it(triple[0] + " % " + triple[1] + " = " + triple[2], function() {
                    var dividend = Integer.parse(triple[0]);
                    var divisor = Integer.parse(triple[1]);
                    var q = new Integer();
                    var r = new Integer();
                    Integer.divRem(dividend, divisor, q, r);
                    assert.strictEqual(triple[2], r.toString());
                });
            })(triples[i]);
        }
    });
});