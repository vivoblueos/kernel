# Windows Instructions

### Prerequisites
Install the openssl prerequisite:
```cmd
git clone https://github.com/microsoft/vcpkg
vcpkg\bootstrap-vcpkg.bat
vcpkg\vcpkg.exe install openssl:x64-windows
vcpkg\vcpkg.exe integrate install
```

### Running Tests
Set the environment variable `VCPKGRS_DYNAMIC=1`, for cmd:
```cmd
set VCPKGRS_DYNAMIC=1
```
or powershell:
```ps
$env:VCPKGRS_DYNAMIC=1
```

It should now be possible to run the tests with `cargo test`.