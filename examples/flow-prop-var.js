// FAIL @ https://flow.org/try

function f(x: number | string): number {
  var y = typeof x === "number";
  if (y) return x + 1; // ERROR: x might be a string
  return 0;
}
