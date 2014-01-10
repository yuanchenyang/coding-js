onmessage = function(event) {
    var result = eval(event.data);
    this.postMessage({'type': 'return_value', 'value': result.toString()});
    this.postMessage({'type': 'end'});
};