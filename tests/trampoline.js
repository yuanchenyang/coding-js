function isFunction(functionToCheck) {
    var getType = {};
    return functionToCheck && getType.toString.call(functionToCheck) === '[object Function]';
}

var variadic = function(fn) {
    return function() {
        return fn(Array.prototype.slice.call(arguments));
    }
}

var trampoline = function (fn) {
    return variadic(function(args) {
        var result = fn.apply(this, args);

        while (result instanceof Function) {
            result = result();
        }

        return result;
    });
};

var even = trampoline(_even),
    odd  = trampoline(_odd);

function _even (n) {
  return n == 0
    ? true
    : function () { return _odd(n - 1); };
};

function _odd (n) {
  return n == 0
    ? false
    : function () { return _even(n - 1); };
};
