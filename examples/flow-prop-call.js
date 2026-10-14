// FAIL @ https://flow.org/try

function isNumber(x: number | string) {
  return (typeof x === "number");
}

function g(x: number | string): number {
  if (isNumber(x)) return x + 1; // ERROR: x might be a string
  return 0;
}
