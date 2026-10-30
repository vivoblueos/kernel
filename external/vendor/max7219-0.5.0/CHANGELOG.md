# CHANGELOG

### 0.5.0

Specify rust edition to `2021`.
Specify rust-version to `1.60`.
Update `embedded-hal` dependency to `v1.0.0` (thanks [SmartBoy84](https://github.com/SmartBoy84))

### 0.4.2

Add `write_raw_byte` to update display in smallest possible increment.

### 0.4.1

Fix edge cases for integer and buffer size for righ justification 

### 0.4.0

Add support for integer display in decimal and hex for i32 
Credit goes to [zignig](https://github.com/zignig)

### 0.3.1

Add support for letter `n`.

### 0.3.0

Refactor `PinError` into `DataError` removing `From` requirements.

### 0.2.2

Fix addressing bug in `write_raw` method.

### 0.2.1

Made `connectors` module public to enable storage. Added `write_raw` support.
Credit goes to [arosspope](https://github.com/arosspope)

### 0.2.0

Initial "redone" release.
