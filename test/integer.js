var chai = require('chai');
var Integer = require('../src/integer.js').Integer;
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

describe("addAssign", function() {

});