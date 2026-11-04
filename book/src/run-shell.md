# Run shell in QEMU

We have implemented a simple shell to demonstrate the functionality of the BlueOS kernel. First let's build the shell executable.
```bash
gn gen out/shell_test --args='board="qemu_mps2_an385" build_type="release"'
ninja -C out/shell_test shell_runner
```
The `ninja` will output a line at last, which is like
```
Generated /build/vivoblueos/out/shell_test/bin/shell_runner-qemu.sh
```
Now we can run the shell via the generated script. If everything is going smooth, we can see
```
Hello, shell!
>
```
Please type `help` for playing with this shell.