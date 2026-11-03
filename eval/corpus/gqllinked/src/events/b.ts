// The twin `Event` model — a second same-named candidate. Two candidates ⇒
// the schema type `Event` is ambiguous and must never be guessed.
export interface Event {
  when: string;
}
