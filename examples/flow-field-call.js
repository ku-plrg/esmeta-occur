// FAIL @ https://flow.org/try (a, d, and e2 are rejected; c and e1 are accepted)

function id(x: number): number { return x; }

// FAIL: the call writes nothing, but the refinement of o.p is dropped
function a(o: { p: ?number }): number {
  if (o.p != null) { id(0); return o.p; } // ERROR: o.p might be null
  return 0;
}

// PASS: a direct write to another property keeps the refinement of o.p
function c(o: { p: ?number, q: number }): number {
  if (o.p != null) { o.q = 1; return o.p; }
  return 0;
}

// FAIL: a write to the same property of a possible alias drops it
function d(o: { p: ?number }, x: { p: ?number }): number {
  if (o.p != null) { x.p = null; return o.p; } // ERROR: o.p might be null
  return 0;
}

// PASS: a call to a closure that writes no variables keeps the refinement of v
function e1(v: ?number): number {
  function f() {}
  if (v != null) { f(); return v; }
  return 0;
}

// FAIL: a call to a closure that writes v drops it
function e2(v: ?number): number {
  function g() { v = null; }
  if (v != null) { g(); return v; } // ERROR: v might be null
  return 0;
}
