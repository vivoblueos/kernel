// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - rmsyn <rmsynchls@gmail.com>

//! System Control Register - EL3
//!
//! Provides top level control of the system, including its memory system, at EL3.

use tock_registers::{
    interfaces::{Readable, Writeable},
    register_bitfields,
};

register_bitfields! {u64,
    pub SCTLR_EL3 [

        /// SP Interrupt Mask enable.
        ///
        /// **When FEAT_NMI is implemented:**
        ///
        /// When SCTLR_EL3.NMI is 1, controls whether PSTATE.SP acts as an
        /// interrupt mask, and controls the value of PSTATE.ALLINT on taking an exception to EL3.
        ///
        /// - 0b0: Does not cause PSTATE.SP to mask interrupts.
        ///        PSTATE.ALLINT is set to 1 on taking an exception to EL3
        ///
        /// - 0b1: When PSTATE.SP is 1 and execution is at EL3, an IRQ or FIQ interrupt that is targeted
        ///        to EL3 is masked regardless of any denotion of Superpriority.
        ///        PSTATE.ALLINT is set to 0 on taking an exception to EL3.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///     architecturally UNKNOWN value.
        SPINTMASK OFFSET(62) NUMBITS(1) [
            NoMask = 0,
            Mask = 1
        ],

        /// Non-maskable Interrupt enable.
        ///
        /// **When FEAT_NMI is implemented:**
        ///
        /// - 0b0: This control does not affect interrupt masking behavior.
        ///
        /// - 0b1: This control enables all of the following:
        ///   - The use of the PSTATE.ALLINT interrupt mask.
        ///   - IRQ and FIQ interrupts to have Superpriority as an additional attribute.
        ///   - PSTATE.SP to be used as an interrupt mask.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to 0.
        NMI OFFSET(61) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ],

        /// Enables the Transactional Memory Extension at EL3.
        ///
        /// **When FEAT_TME is implemented:**
        ///
        /// - 0b0: Any attempt to execute a TSTART instruction at EL3 is trapped, unless HCR_EL2.TME
        ///        or SCR_EL3.TME causes TSTART instructions to be UNDEFINED at EL3.
        ///
        /// - 0b1: This control does not cause any TSTART instruction to be trapped.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///        architecturally UNKNOWN value.
        TME OFFSET(53) NUMBITS(1) [
            Trap = 0,
            NoTrap = 1
        ],

        /// Forces a trivial implementation of the Transactional Memory Extension at EL3.
        ///
        /// **When FEAT_TME is implemented:**
        ///
        /// - 0b0: This control does not cause any TSTART instruction to fail.
        ///
        /// - 0b1: When the TSTART instruction is executed at EL3, the transaction fails with a TRIVIAL
        ///        failure cause.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///        architecturally UNKNOWN value
        TMT OFFSET(51) NUMBITS(1) [
            NoFail = 0,
            Fail = 1
        ],

        /// Default PSTATE.SSBS value on Exception Entry.
        ///
        /// **When FEAT_SSBS is implemented:**
        ///
        /// - 0b0: PSTATE.SSBS is set to 0 on an exception to EL3.
        ///
        /// - 0b1: PSTATE.SSBS is set to 1 on an exception to EL3.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset,this field resets to an IMPLEMENTATION DEFINED value.
        DSSBS OFFSET(44) NUMBITS(1) [
            SsbsUnset = 0,
            SsbsSet   = 1
        ],

        /// Allocation Tag Access in EL3.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Controls access to Allocation Tags and Tag Check operations in EL3.
        ///
        /// - 0b0: Access to Allocation Tags is prevented at EL3.
        ///        Memory accesses at EL3 are not subject to a Tag Check operation.
        ///
        /// - 0b1: This control does not prevent access to Allocation Tags at EL3.
        ///        Tag Checked memory accesses at EL3 are subject to a Tag Check operation.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        ATA OFFSET(43) NUMBITS(1) [
            Prevent = 0,
            NoPrevent = 1
        ],

        /// Tag Check Fault in EL3.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// Controls the effect of Tag Check Faults due to Loads and Stores in EL3.
        /// If FEAT_MTE3 is not implemented, the value 0b11 is reserved.
        ///
        /// - 0b00: Tag Check Faults have no effect on the PE.
        ///
        /// - 0b01: Tag Check Faults cause a synchronous exception.
        ///
        /// - 0b10: Tag Check Faults are asynchronously accumulated.
        ///
        /// - 0b11: When FEAT_MTE3 is implemented:
        ///         Tag Check Faults cause a synchronous exception on reads, and are asynchronously
        ///         accumulated on writes.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        TCF OFFSET(40) NUMBITS(2) [
            NoEffect = 0,
            SyncException = 1,
            AsyncAccumulated = 2,
            SyncReadAsyncWrite = 3
        ],

        /// When synchronous exceptions are not being generated by Tag Check Faults, this field controls
        /// whether on exception entry into EL3, all Tag Check Faults due to instructions executed before
        /// exception entry, that are reported asynchronously, are synchronized into TFSRE0_EL1 and
        /// TFSR_ELx registers.
        ///
        /// **When FEAT_MTE2 is implemented:**
        ///
        /// - 0b0: Tag Check Faults are not synchronized on entry to EL3.
        ///
        /// - 0b1: Tag Check Faults are synchronized on entry to EL3.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        ITFSB OFFSET(37) NUMBITS(1) [
            NoSyncEntry = 0,
            SyncEntry = 1
        ],

        /// PAC Branch Type compatibility at EL3.
        ///
        /// **When FEAT_BTI is implemented:**
        ///
        /// - 0b0: When the PE is executing at EL3, PACIASP and PACIBSP are compatible with
        ///        PSTATE.BTYPE == 0b11.
        ///
        /// - 0b1: When the PE is executing at EL3, PACIASP and PACIBSP are not compatible with
        ///        PSTATE.BTYPE == 0b11.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        BT OFFSET(36) NUMBITS(1) [
            Compat = 0,
            NoCompat = 1
        ],

        /// Controls enabling of pointer authentication (using the APIAKey_EL1 key) of instruction addresses
        /// in the EL3 translation regime.
        ///
        /// **When FEAT_PAuth is implemented:**
        ///
        /// Possible values of this bit are:
        ///
        /// - 0b0: Pointer authentication (using the APIAKey_EL1 key) of instruction addresses is not
        ///        enabled.
        ///
        /// - 0b1: Pointer authentication (using the APIAKey_EL1 key) of instruction addresses is
        ///        enabled.
        ///
        /// For more information, see Pointer authentication on page D5-4775.
        ///
        /// Note
        ///
        /// This field controls the behavior of the AddPACIA and AuthIA pseudocode functions. Specifically,
        /// when the field is 1, AddPACIA returns a copy of a pointer to which a pointer authentication code
        /// has been added, and AuthIA returns an authenticated copy of a pointer. When the field is 0, both of
        /// these functions are NOP.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        EnIA OFFSET(31) NUMBITS(1) [
            NotEnabled = 0,
            Enabled = 1
        ],

        /// Controls enabling of pointer authentication (using the APIBKey_EL1 key) of instruction addresses
        /// in the EL3 translation regime.
        ///
        /// **When FEAT_PAuth is implemented:**
        ///
        /// Possible values of this bit are:
        ///
        /// - 0b0: Pointer authentication (using the APIBKey_EL1 key) of instruction addresses is not
        ///        enabled.
        ///
        /// - 0b1: Pointer authentication (using the APIBKey_EL1 key) of instruction addresses is
        ///        enabled.
        ///
        /// For more information, see Pointer authentication on page D8-5164.
        ///
        /// Note
        ///
        /// This field controls the behavior of the AddPACIB and AuthIB pseudocode functions. Specifically,
        /// when the field is 1, AddPACIB returns a copy of a pointer to which a pointer authentication code
        /// has been added, and AuthIB returns an authenticated copy of a pointer. When the field is 0, both of
        /// these functions are NOP.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        EnIB OFFSET(30) NUMBITS(1) [
            NotEnabled = 0,
            Enabled = 1
        ],

        /// Controls enabling of pointer authentication (using the APDAKey_EL1 key) of instruction addresses
        /// in the EL3 translation regime.
        ///
        /// **When FEAT_PAuth is implemented:**
        ///
        /// - 0b0: Pointer authentication (using the APDAKey_EL1 key) of data addresses is not enabled.
        ///
        /// - 0b1: Pointer authentication (using the APDAKey_EL1 key) of data addresses is enabled.
        ///
        /// For more information, see Pointer authentication on page D8-5164.
        ///
        /// Note
        ///
        /// This field controls the behavior of the AddPACDA and AuthDA pseudocode functions. Specifically,
        /// when the field is 1, AddPACDA returns a copy of a pointer to which a pointer authentication code
        /// has been added, and AuthDA returns an authenticated copy of a pointer. When the field is 0, both
        /// of these functions are NOP.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        EnDA OFFSET(27) NUMBITS(1) [
            NotEnabled = 0,
            Enabled = 1
        ],

        /// Endianness of data accesses at EL3, and stage 1 translation table walks in the EL3 translation
        /// regime.
        ///
        /// - 0b0: Explicit data accesses at EL3, and stage 1 translation table walks in the EL3 translation
        ///        regime are little-endian.
        ///
        /// - 0b1: Explicit data accesses at EL3, and stage 1 translation table walks in the EL3 translation
        ///        regime are big-endian.
        ///
        /// If an implementation does not provide Big-endian support at Exception levels higher than EL0, this
        /// bit is RES 0.
        ///
        /// If an implementation does not provide Little-endian support at Exception levels higher than EL0,
        /// this bit is RES 1.
        ///
        /// The EE bit is permitted to be cached in a TLB.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset,this field resets to an IMPLEMENTATION DEFINED value.
        EE OFFSET(25) NUMBITS(1) [
            Little = 0,
            Big = 1
        ],

        /// Exception Entry is Context Synchronizing.
        ///
        /// **When FEAT_ExS is implemented:**
        ///
        /// - 0b0: The taking of an exception to EL3 is not a context synchronizing event.
        ///
        /// - 0b1: The taking of an exception to EL3 is a context synchronizing event.
        ///
        /// If SCTLR_EL3.EIS is set to 0b0:
        /// - Indirect writes to ESR_EL3, FAR_EL3, SPSR_EL3, ELR_EL3 are synchronized on
        ///   exception entry to EL3, so that a direct read of the register after exception entry sees the
        ///   indirectly written value caused by the exception entry.
        ///
        /// - Memory transactions, including instruction fetches, from an Exception level always use the
        ///   translation resources associated with that translation regime.
        ///
        /// - Exception Catch debug events are synchronous debug events.
        ///
        /// - DCPS* and DRPS instructions are context synchronization events.
        ///   The following are not affected by the value of SCTLR_EL3.EIS:
        ///
        /// - Changes to the PSTATE information on entry to EL3.
        ///
        /// - Behavior of accessing the banked copies of the stack pointer using the SP register name for
        ///   loads, stores and data processing instructions.
        ///
        /// - Debug state exit.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        EIS OFFSET(22) NUMBITS(1) [
            NotContextSync = 0,
            Context = 1
        ],

        /// Implicit Error Synchronization event enable.
        ///
        /// **When FEAT_IESB is implemented:**
        ///
        /// - 0b0: Disabled.
        ///
        /// - 0b1: An implicit error synchronization event is added:
        ///     - At each exception taken to EL3.
        ///     - Before the operational pseudocode of each ERET instruction executed at EL3.
        ///
        /// When the PE is in Debug state, the effect of this field is CONSTRAINED UNPREDICTABLE, and its
        /// Effective value might be 0 or 1 regardless of the value of the field and, if implemented,
        /// SCR_EL3.NMEA. If the Effective value of the field is 1, then an implicit error synchronization
        /// event is added after each DCPSx instruction taken to EL3 and before each DRPS instruction executed
        /// at EL3, in addition to the other cases where it is added.
        ///
        /// When FEAT_DoubleFault is implemented, the PE is in Non-debug state, and the Effective value of
        /// SCR_EL3.NMEA is 1, this field is ignored and its Effective value is 1.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        IESB OFFSET(21) NUMBITS(1) [
            Disabled = 0,
            Enabled = 1
        ],

        /// Write permission implies XN (Execute-never).
        ///
        /// For the EL3 translation regime, this bit can force all
        /// memory regions that are writable to be treated as XN.
        ///
        /// - 0b0: This control has no effect on memory access permissions.
        ///
        /// - 0b1: Any region that is writable in the EL3 translation regime is forced to XN for accesses
        ///        from software executing at EL3.
        ///
        /// This bit applies only when SCTLR_EL3.M bit is set.
        ///
        /// The WXN bit is permitted to be cached in a TLB.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        WXN OFFSET(19) NUMBITS(1) [
            Disabled = 0,
            Enabled = 1
        ],

        /// Controls enabling of pointer authentication (using the APDBKey_EL1 key) of instruction addresses
        /// in the EL3 translation regime.
        ///
        /// **When FEAT_PAuth is implemented:**
        ///
        /// - 0b0: Pointer authentication (using the APDBKey_EL1 key) of data addresses is not enabled.
        ///
        /// - 0b1: Pointer authentication (using the APDBKey_EL1 key) of data addresses is enabled.
        ///
        /// For more information, see Pointer authentication on page D8-5164.
        ///
        /// Note
        ///
        /// This field controls the behavior of the AddPACDB and AuthDB pseudocode functions. Specifically,
        /// when the field is 1, AddPACDB returns a copy of a pointer to which a pointer authentication code
        /// has been added, and AuthDB returns an authenticated copy of a pointer. When the field is 0, both of
        /// these functions are NOP.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        EnDB OFFSET(13) NUMBITS(1) [
            Disabled = 0,
            Enabled = 1
        ],

        /// Instruction access Cacheability control, for accesses at EL3.
        ///
        /// - 0b0: All instruction access to Normal memory from EL3 are Non-cacheable for all levels of
        ///        instruction and unified cache.
        ///
        ///        If the value of SCTLR_EL3.M is 0, instruction accesses from stage 1 of the EL3
        ///        translation regime are to Normal, Outer Shareable, Inner Non-cacheable, Outer
        ///        Non-cacheable memory.
        ///
        /// - 0b1: This control has no effect on the Cacheability of instruction access to Normal memory
        ///        from EL3.
        ///
        ///        If the value of SCTLR_EL3.M is 0, instruction accesses from stage 1 of the EL3
        ///        translation regime are to Normal, Outer Shareable, Inner Write-Through, Outer
        ///        Write-Through memory.
        ///
        /// This bit has no effect on the EL1&0, EL2, or EL2&0 translation regimes.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to 0.
        I OFFSET(12) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1
        ],

        /// Exception Exit is Context Synchronizing.
        ///
        /// **When FEAT_ExS is implemented:**
        ///
        /// - 0b0: An exception return from EL3 is not a context synchronizing event
        ///
        /// - 0b1: An exception return from EL3 is a context synchronizing event
        ///
        /// If SCTLR_EL3.EOS is set to 0b0:
        /// - Memory transactions, including instruction fetches, from an Exception level always use the
        ///   translation resources associated with that translation regime.
        ///
        /// - Exception Catch debug events are synchronous debug events.
        ///
        /// - DCPS* and DRPS instructions are context synchronization events.
        ///
        ///
        /// The following are not affected by the value of SCTLR_EL3.EOS:
        /// - The indirect write of the PSTATE and PC values from SPSR_EL3 and ELR_EL3 on
        ///        exception return is synchronized.
        ///
        /// - If the PE enters Debug state before the first instruction after an Exception return from EL3
        ///   to Non-secure state, any pending Halting debug event completes execution.
        ///
        /// - The GIC behavior that allocates interrupts to FIQ or IRQ changes simultaneously with
        ///        leaving the EL3 Exception level.
        ///
        /// - Behavior of accessing the banked copies of the stack pointer using the SP register name for
        ///        loads, stores and data processing instructions.
        ///
        /// - Exit from Debug state.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///        architecturally UNKNOWN value.
        EOS OFFSET(11) NUMBITS(1) [
            NotContextSync = 0,
            ContextSync = 1
        ],

        /// Non-aligned access.
        ///
        /// **When FEAT_LSE2 is implemented:**
        ///
        /// This bit controls generation of Alignment faults at EL3 under certain
        /// conditions. The following instructions generate an Alignment fault if all bytes being accessed are
        /// not within a single 16-byte quantity, aligned to 16 bytes for access:
        ///
        /// - LDAPR, LDAPRH, LDAPUR, LDAPURH, LDAPURSH, LDAPURSW, LDAR, LDARH, LDLAR, LDLARH.
        /// - STLLR, STLLRH, STLR, STLRH, STLUR, and STLURH
        ///
        /// If FEAT_LRCPC3 is implemented, the following instructions generate an Alignment fault
        /// if all bytes being accessed for a single register are not within a single 16-byte quantity, aligned to 16 bytes for access:
        ///
        /// - LDIAPP, STILP, the post index versions of LDAPR and the pre index versions of STLR.
        /// - If Advanced SIMD and floating-point instructions are implemented, LDAPUR (SIMD&FP), LDAP1 (SIMD&FP), STLUR (SIMD&FP), and STL1 (SIMD&FP).
        ///
        /// Possible values of this bit are:
        /// - 0b0: Unaligned accesses by the specified instructions generate an Alignment fault.
        /// - 0b1: Unaligned accesses by the specified instructions do not generate an Alignment fault.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        nAA OFFSET(6) NUMBITS(1) [
            Fault = 0,
            NoFault = 1
        ],

        /// SP Alignment check enable.
        ///
        /// When set to 1, if a load or store instruction executed at EL3 uses the
        /// SP as the base address and the SP is not aligned to a 16-byte boundary, then a SP alignment fault
        /// exception is generated. For more information, see SP alignment checking on page D1-4668.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        SA OFFSET(3) NUMBITS(1) [
            NoFault = 0,
            Fault = 1
        ],

        /// Cacheability control, for data accesses.
        ///
        /// - 0b0: All data access to Normal memory from EL3, and all Normal memory accesses to the
        ///        EL3 translation tables, are Non-cacheable for all levels of data and unified cache.
        ///
        /// - 0b1: This control has no effect on the Cacheability of:
        ///   - Data access to Normal memory from EL3.
        ///   - Normal memory accesses to the EL3 translation tables.
        ///
        /// This bit has no effect on the EL1&0, EL2, or EL2&0 translation regimes.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to 0.
        C OFFSET(2) NUMBITS(1) [
            Enabled = 0,
            Disabled = 1
        ],

        /// Alignment check enable.
        ///
        /// This is the enable bit for Alignment fault checking at EL3.
        ///
        /// - 0b0: Alignment fault checking disabled when executing at EL3.
        ///
        ///        Instructions that load or store one or more registers, other than load/store exclusive and
        ///        load-acquire/store-release, do not check that the address being accessed is aligned to the
        ///        size of the data element(s) being accessed.
        ///
        /// - 0b1: Alignment fault checking enabled when executing at EL3.
        ///
        ///        All instructions that load or store one or more registers have an alignment check that the
        ///        address being accessed is aligned to the size of the data element(s) being accessed. If
        ///        this check fails it causes an Alignment fault, which is taken as a Data Abort exception.
        ///
        /// Load/store exclusive and load-acquire/store-release instructions have an alignment check regardless
        /// of the value of the A bit.
        ///
        /// If FEAT_MOPS is implemented,SETG* instructions have an alignment check regardless of the
        /// value of the A bit.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to an
        ///   architecturally UNKNOWN value.
        A OFFSET(1) NUMBITS(1) [
            Disabled = 0,
            Enabled = 1
        ],

        /// MMU enable for EL3 stage 1 address translation.
        ///
        /// Possible values of this bit are:
        ///
        /// - 0b0: EL3 stage 1 address translation disabled.
        ///
        ///    See the SCTLR_EL3.I field for the behavior of instruction accesses to Normal memory.
        ///
        /// - 0b1: EL3 stage 1 address translation enabled.
        ///
        /// The reset behavior of this field is:
        /// - On a Warm reset, in a system where the PE resets into EL3, this field resets to 0.
        M OFFSET(0) NUMBITS(1) [
            Disabled = 0,
            Enabled = 1
        ]
    ]
}

pub struct Reg;

impl Readable for Reg {
    type T = u64;
    type R = SCTLR_EL3::Register;

    sys_coproc_read_raw!(u64, "SCTLR_EL3", "x");
}

impl Writeable for Reg {
    type T = u64;
    type R = SCTLR_EL3::Register;

    sys_coproc_write_raw!(u64, "SCTLR_EL3", "x");
}

pub const SCTLR_EL3: Reg = Reg {};
