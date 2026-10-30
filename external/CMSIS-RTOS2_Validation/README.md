# CMSIS-RTOS2 Validation

This repository contains a test suite that validates CMSIS-RTOS2 implementations. It uses [**Arm Virtual Hardware**](https://www.arm.com/virtual-hardware) to run a CI/CD flow to verify correct operation of the real-time operating systems (RTOS) under test on various Arm Cortex-M based processors.

**Arm Virtual Hardware** provides simulation models, software tooling, and infrastructure that can be integrated into CI/CD and MLOps development flows. The simulation models (called Arm Virtual Hardware Targets) are an implementation of a Cortex-M device sub-systems and are designed for complex software verification and testing. This allows simulation-based test automation of various software workloads, including unit tests, integration tests, and fault injection. Refer to the [Arm Virtual Hardware documentation](https://arm-software.github.io/AVH/main/overview/html/index.html) for more information.

## Repository structure

| Directory         | Contents                                                                          |
|-------------------|-----------------------------------------------------------------------------------|
| .github/workflows | Workflow YML files for running the test suite and for creating the documentation. |
| Doxygen           | Doxygen input files for creating the documentation.                               |
| Include           | Include files for test cases etc.                                                 |
| Layer             | Layers for creating the projects.                                                 |
| Project           | An example project that shows unit testing.                                       |
| Script            | Various shell scripts.                                                            |
| Source            | Test case source code.                                                            |

## Test matrix

Currently, the following tests are executed in the [CMSIS_RV2](./.github/workflows/cmsis_rv2.yml) workflow:

| RTOS     |  Device   | Compiler        |
|----------|-----------|-----------------|
| FreeRTOS |  ARMCM0P  | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM3   | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM4   | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM7   | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM23  | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM33  | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM55  | AC6, GCC, CLANG |
| FreeRTOS |  ARMCM85  | AC6, GCC, CLANG |
| RTX5     |  ARMCM0P  | AC6, GCC, CLANG |
| RTX5     |  ARMCM3   | AC6, GCC, CLANG |
| RTX5     |  ARMCM4   | AC6, GCC, CLANG |
| RTX5     |  ARMCM7   | AC6, GCC, CLANG |
| RTX5     |  ARMCM23  | AC6, GCC, CLANG |
| RTX5     |  ARMCM33  | AC6, GCC, CLANG |
| RTX5     |  ARMCM55  | AC6, GCC, CLANG |
| RTX5     |  ARMCM85  | AC6, GCC, CLANG |

## License

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
