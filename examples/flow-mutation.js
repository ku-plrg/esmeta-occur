// PASS @ https://flow.org/try

function f(x: number | string, y: any): number {
  y = x;
  if (typeof y === "number") return y + 1;
  return 0;
}
