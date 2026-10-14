// FAIL @ https://flow.org/try

function f(x: number | string): number {
  var y = (typeof x === "number") ? "abc" : 42;
  if (typeof y === "number") return x.length; // ERROR: x might be a string
  return x + 1; // ERROR: x might be a number
}
