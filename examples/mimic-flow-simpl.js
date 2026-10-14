// FAIL @ https://flow.org/try

type ESValue = mixed; type Object = string;
function LengthOfArrayLike(obj: Object): mixed { /* ... */ }
function IsArray(argument: mixed): Boolean {
  return typeof argument === 'string';            // No propagation to call-sites
}
function FlattenIntoArray(element: ESValue): any {
  let shouldFlatten = IsArray(element);           // No propagation to variables
  if (shouldFlatten) LengthOfArrayLike(element);  // `element` should be `Object` but `ESValue`
}
