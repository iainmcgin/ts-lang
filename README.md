TS0 - A toy language with typestate inference
------------------------------------------------

TS0 is a toy language with typestate inference, built and studied as part of
the PhD Thesis of the author (Iain McGinniss).

Should you wish to reuse any of the source code in this language implementation,
feel free to do so under the terms of the Simplified BSD License (see
file COPYING for details).

Miscellanea
===========

### Package structure
The root package "uk.ac.gla.dcs" is hosted directly under the "scala" source
directories in both "main" and "test", i.e. there is no directory structure
uk/ac/gla/dcs as would be the normal Java convention. This is because I find
such deeply nested directory structures annoying, especially for such a small
project as this.