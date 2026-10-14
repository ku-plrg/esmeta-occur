// FAIL @ https://flow.org/try

type ESValue = mixed; type Object = string;
type Completion = { Type: string, Value: mixed };
function LengthOfArrayLike(obj: Object): mixed { /* ... */ }
function IsArray(argument: mixed): Completion {
  if (typeof argument !== 'string') return { Type: "Normal", Value: false };
  else if (Math.random() > 0.5) return { Type: "Throw", Value: "Error" };
  else return { Type: "Normal", Value: true };
} // No propagation to call-sites
function FlattenIntoArray(element: ESValue): any {
  let shouldFlatten = IsArray(element); // No propagation to variables
  if (shouldFlatten.Type === "Normal" && shouldFlatten.Value)
    LengthOfArrayLike(element); // `element` should be `Object` but `ESValue`
}
