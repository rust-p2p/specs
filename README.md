# Specs
Models various aspects of the protocols implemented in the `rust-p2p` org.

## Organization
Spec `$` is contained in a file `$.tla`. A file named `MC$.tla` extends
the spec `$` with constraints to allow model checking with `tlc`. The `tlc`
configuration can be found in `MC$.cfg`. To execute the model checker run
`tlc MC$.tla`. The `tla-tools` can be installed on arch linux using
`yay -S tla-tools`.

`test` runs tests specified in a file `MCTest` and formats the output of `tlc`.
`state` prints complete state after a specified test. Requires `rc` and `ssam` from `plan9port`.

## Search path
To add a directory to the search path set the `TLA_JAVA_OPTS` variable.

```sh
cd examples
TLA_JAVA_OPTS="-DTLA-Library=../utils" tlc Ping.tla
```

## License
ISC License

Copyright (c) 2019, David Craven and others

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
