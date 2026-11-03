// Host-language implementations for the civic schema.
// - `Assertion` (interface) uniquely models the schema type `Assertion`.
// - `assertion` (function) uniquely resolves the schema field `Query.assertion`.
// - `Widget` (function) shares a name with the schema TYPE `Widget`, but a type
//   cannot be satisfied by a function — the linker must NOT link them.

export interface Assertion {
  id: number;
}

export function assertion(id: number): Assertion {
  return { id };
}

export function Widget(): number {
  return 0;
}
