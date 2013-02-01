super chobo Racket version
===================================

Halp!!

I don't know Racket very well--how do you do something equivalent to
Scheme's load, or are you required to use modules?

Anyway, the only way I could get things to work was to combine
racket-compat.scm, mk.scm, and mk-rd.scm into this one giant file,
superchobo.scm.  Yuck!  But loading this file in DrRacket *does* work.

Also, these files should really be Racket, not Scheme, and probably
most or all of racket-compat should be replaced with calls to Racket
library functions.

I'd appreciate anypony who ported these files to actual Racket style.  Thanks!

--Will
