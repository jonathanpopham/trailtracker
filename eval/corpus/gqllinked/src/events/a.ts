// One of two same-named `Event` models. Its twin in ./b.ts makes the schema
// type `Event` ambiguous, so the linker preserves the ambiguity (no edge).
export interface Event {
  id: number;
}
