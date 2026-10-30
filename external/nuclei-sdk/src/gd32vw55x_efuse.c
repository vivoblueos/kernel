/*!
    \file    gd32vw55x_efuse.c
    \brief   EFUSE driver

    \version 2023-07-20, V1.0.0, firmware for GD32VW55x
*/

/*
    Copyright (c) 2023, GigaDevice Semiconductor Inc.

    Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

    1. Redistributions of source code must retain the above copyright notice, this
       list of conditions and the following disclaimer.
    2. Redistributions in binary form must reproduce the above copyright notice,
       this list of conditions and the following disclaimer in the documentation
       and/or other materials provided with the distribution.
    3. Neither the name of the copyright holder nor the names of its contributors
       may be used to endorse or promote products derived from this software without
       specific prior written permission.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
OF SUCH DAMAGE.
*/

#include "gd32vw55x_efuse.h"

/*!
    \brief      read EFUSE value
    \param[in]  ef_addr: EFUSE address, the starting address of each parameter segment, in bytes
      \arg        0~0x60
    \param[in]  size: size of EFUSE, in bytes
      \arg        1~0x20
    \param[out] buf: the buffer for storing read-out EFUSE register value
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_read(uint32_t ef_addr, uint32_t size, uint32_t buf[])
{
    uint32_t i = 0U;
    uint32_t timeout = 0xFFU;
    uint32_t reg_addr = 0U;
    uint32_t number = size / 4U;

    if(0U == number) {
        number = 1U;
    }

    /* assert EFUSE address and size parameter */
    if((END_ADDR < ef_addr) || (size > EFUSE_MAX_SIZE)) {
        return ERROR;
    }

    /* get the register address corresponding to EFUSE */
    if(0x4U > ef_addr) {
        reg_addr = (uint32_t)(EFUSE + 0x08U + (ef_addr * 4U));
    } else {
        /* when EFUSE address is greater than 4, it must be an integral multiple of 4 */
        if(0U == (ef_addr % 4U)) {
            reg_addr = (uint32_t)(EFUSE + 0x14U + ef_addr);
        } else {
            return ERROR;
        }
    }

    /* EFUSE read operation */
    EFUSE_CS &= (~EFUSE_CS_EFRW);
    /* write EFUSE address and size */
    EFUSE_ADDR = (uint32_t)((size << 8U) | ef_addr);
    /* start read EFUSE operation */
    EFUSE_CS |= EFUSE_CS_EFSTR;

    /* wait for the operation to complete */
    do {
        timeout--;
    } while((RESET == efuse_flag_get(EFUSE_RDIF)) && (0x00U != timeout));
    if(0x00U == timeout) {
        return ERROR;
    }

    /* read EFUSE */
    for(i = 0U; i < number; i++) {
        buf[i] = REG32(reg_addr + (4U * i));
    }

    /* clear EFUSE read completed flag */
    EFUSE_CS |= (uint32_t)EFUSE_CS_RDIC;

    return SUCCESS;
}

/*!
    \brief      write EFUSE
    \param[in]  ef_addr: EFUSE address, the starting address of each parameter segment, in bytes.
                         When ef_addr is greater than 4, the ef_addr must be an integral multiple of 4
      \arg        0~0x60
    \param[in]  size: size of EFUSE, in bytes
      \arg        1~0x20
    \param[in]  buf: the buffer of data written to EFUSE
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_write(uint32_t ef_addr, uint32_t size, uint32_t buf[])
{
    uint32_t i = 0U;
    uint32_t timeout = 0xFFFFU;
    uint32_t reg_addr = 0U;
    uint32_t number = size / 4U;

    if(0U == number) {
        number = 1U;
    }

    /* assert EFUSE address and size parameter */
    if((END_ADDR < ef_addr) || (size > EFUSE_MAX_SIZE)) {
        return ERROR;
    }

    /* PUID and HUK are not modifiable */
    if((MCU_UID_ADDR <= ef_addr) && (ef_addr < USER_DATA_ADDR)) {
        return ERROR;
    }

    /* get the register address corresponding to EFUSE */
    if(0x4U > ef_addr) {
        reg_addr = (uint32_t)(EFUSE + 0x08U + (ef_addr * 4U));
    } else {
        /* when EFUSE address is greater than 4, it must be an integral multiple of 4 */
        if(ef_addr % 4U) {
            return ERROR;
        } else {
            reg_addr = (uint32_t)(EFUSE + 0x14U + ef_addr);
        }
    }

    /* EFUSE power on */
    RCU_CFG1 |= RCU_CFG1_BGPU;
    /* EFUSE write operation */
    EFUSE_CS |= EFUSE_CS_EFRW;
    /* write EFUSE address and size */
    EFUSE_ADDR = (uint32_t)((size << 8U) | ef_addr);
    /* write EFUSE */
    for(i = 0U; i < number; i++) {
        REG32(reg_addr + (4U * i)) = buf[i];
    }
    /* start write EFUSE operation */
    EFUSE_CS |= EFUSE_CS_EFSTR;

    /* wait for the operation to complete */
    do {
        timeout--;
    } while((RESET == efuse_flag_get(EFUSE_PGIF)) && (0x00U != timeout));
    if(0x00U == timeout) {
        return ERROR;
    }

    /* clear EFUSE write operation flag */
    EFUSE_CS &= (~EFUSE_CS_EFRW);
    /* clear EFUSE write completed flag*/
    EFUSE_CS |= (uint32_t)EFUSE_CS_PGIC;
    /* EFUSE power off */
    RCU_CFG1 &= (~RCU_CFG1_BGPU);

    return SUCCESS;
}

/*!
    \brief      configure boot
    \param[in]  size: size of data(byte)
      \arg        the size must be 1
    \param[in]  bt_value: the value of boot configuration
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_boot_config(uint32_t size, uint8_t bt_value[])
{
    if(size != 1U) {
        return ERROR;
    }
    return efuse_write(EFUSE_CTL0_ADDR, size, (uint32_t *)bt_value);
}

/*!
    \brief      configure efuse control1
    \param[in]  size: size of data(byte)
      \arg      the size must be 1
    \param[in]  ctl: control value
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_control1_config(uint32_t size, uint8_t ctl[])
{
    if(size != 1U) {
        return ERROR;
    }
    return efuse_write(EFUSE_CTL1_ADDR, size, (uint32_t *)ctl);
}

/*!
    \brief      configure flash protection
    \param[in]  size: size of data(byte)
      \arg        the size must be 1
    \param[in]  fp_value: flash protection value
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_fp_config(uint32_t size, uint8_t fp_value[])
{
    if(size != 1U) {
        return ERROR;
    }
    return efuse_write(FP_ADDR, size, (uint32_t *)fp_value);
}

/*!
    \brief      configure user control
    \param[in]  size: size of data(byte)
      \arg        the size must be 1
    \param[in]  user_ctl: user control value
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_user_control_config(uint32_t size, uint8_t user_ctl[])
{
    if(size != 1U) {
        return ERROR;
    }
    return efuse_write(USER_CTL_ADDR, size, (uint32_t *)user_ctl);
}

/*!
    \brief      write MCU reserved value
    \param[in]  size: size of data(byte)
      \arg        the size must be 12
    \param[in]  buf: MCU reserved value
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_res_write(uint32_t size, uint8_t buf[])
{
    if(size != 12U) {
        return ERROR;
    }
    return efuse_write(RESERVED_ADDR, size, (uint32_t *)buf);
}

/*!
    \brief      write AES key
    \param[in]  size: size of data(byte)
      \arg        the size must be 16
    \param[in]  buf: the buffer of data written to efuse
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_aes_key_write(uint32_t size, uint8_t buf[])
{
    if(size != 16U) {
        return ERROR;
    }
    return efuse_write(AES_KEY_ADDR, size, (uint32_t *)buf);
}

/*!
    \brief      write ROTPK key
    \param[in]  size: size of data(byte)
      \arg        the size must be 32
    \param[in]  buf: the buffer of data written to efuse
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_rotpk_key_write(uint32_t size, uint8_t buf[])
{
    if(size != 32U) {
        return ERROR;
    }
    return efuse_write(ROTPK_ADDR, size, (uint32_t *)buf);
}

/*!
    \brief      write user data
    \param[in]  size: size of data(byte)
      \arg        the size must be 32
    \param[in]  buf: the buffer of data written to efuse
    \param[out] none
    \retval     ErrStatus: ERROR or SUCCESS
*/
ErrStatus efuse_user_data_write(uint32_t size, uint8_t buf[])
{
    if(size != 32U) {
        return ERROR;
    }
    return efuse_write(USER_DATA_ADDR, size, (uint32_t *)buf);
}

/*!
    \brief      read MCU reserved value
    \param[in]  none
    \param[out] buf: MCU reserved value after system reset
    \retval     none
*/
void efuse_res_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 3U; i++) {
        buf[i] = REG32(EFUSE + 0x18U + 0x04U * i);
    }
}

/*!
    \brief      read AES key
    \param[in]  none
    \param[out] buf: AES_KEY data after system reset
    \retval     none
*/
void efuse_aes_key_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 4U; i++) {
        buf[i] = REG32(EFUSE + 0x24U + 0x04U * i);
    }
}

/*!
    \brief      read ROTPK key
    \param[in]  none
    \param[out] buf: rotpk_key data after system reset
    \retval     none
*/
void efuse_rotpk_key_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 8U; i++) {
        buf[i] = REG32(EFUSE + 0x34U + 0x04U * i);
    }
}

/*!
    \brief      read puid
    \param[in]  none
    \param[out] buf: puid data after system reset
    \retval     none
*/
void efuse_puid_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 4U; i++) {
        buf[i] = REG32(EFUSE + 0x54U  + 0x04U * i);
    }
}

/*!
    \brief      read huk key
    \param[in]  none
    \param[out] buf: huk key data after system reset
    \retval     none
*/
void efuse_huk_key_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 4U; i++) {
        buf[i] = REG32(EFUSE + 0x64U + 0x04U * i);
    }
}

/*!
    \brief      read user data
    \param[in]  none
    \param[out] buf: user data after system reset
    \retval     none
*/
void efuse_user_data_read(uint32_t buf[])
{
    uint8_t i = 0U;
    for(i = 0U; i < 8U; i++) {
        buf[i] = REG32(EFUSE + 0x74U + 0x04U * i);
    }
}

/*!
    \brief      get boot address information
    \param[in]  none
    \param[out] none
    \retval     current boot address
*/
uint32_t efuse_boot_address_get(void)
{
    return EFUSE_BOOTADDR;
}

/*!
    \brief      lock efuse filed
    \param[in]  source: specifies filed to lock
                one parameter can be selected which is shown as below:
      \arg        EFUSE_BOOT_LOCK: EFUSE boot bits lock bit
      \arg        EFUSE_OPTION_BYTE_LOCK: option byte lock bit
      \arg        EFUSE_ROTPKKEY_LOCK: EFUSE_ROTPK_KEY register lock bit
      \arg        EFUSE_USER_DATA_LOCK: EFUSE_USER_DATA register lock bit
      \arg        EFUSE_AESKEY_LOCK: lock EFUSE_AES_KEY register and enable AES decrypt function
      \arg        EFUSE_FPCTL_USERCTL_LOCK: EFUSE_FPCTL and EFUSE_USER_CTL register lock bit
    \param[out] none
    \retval     none
*/
void efuse_lock_config(efuse_reg_lock_enum source)
{
    uint32_t temp;
    temp = source;
    if(source == EFUSE_BOOT_LOCK) {
        efuse_write(EFUSE_CTL0_ADDR, 1U, &temp);
    } else if(source == EFUSE_ROTPKKEY_LOCK) {
        efuse_write(EFUSE_CTL1_ADDR, 1U, &temp);
    } else if(source == EFUSE_USER_DATA_LOCK) {
        efuse_write(USER_CTL_ADDR, 1U, &temp);
    } else if(source == EFUSE_AESKEY_LOCK) {
        efuse_write(USER_CTL_ADDR, 1U, &temp);
    } else if(source == EFUSE_FPCTL_USERCTL_LOCK) {
        efuse_write(USER_CTL_ADDR, 1U, &temp);
    }
}

/*!
    \brief      check EFUSE flag is set or not
    \param[in]  flag: specifies to get a flag
                only one parameter can be selected which is shown as below:
      \arg        EFUSE_PGIF: programming operation completion flag
      \arg        EFUSE_RDIF: read operation completion flag
      \arg        EFUSE_OVBERIF: overstep boundary error flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus efuse_flag_get(efuse_flag_enum flag)
{
    if(EFUSE_CS & (uint32_t)flag) {
        return SET;
    } else {
        return RESET;
    }
}

/*!
    \brief      clear EFUSE pending flag
    \param[in]  flag: specifies to clear a flag
                only one parameter can be selected which is shown as below:
      \arg        EFUSE_PGIC: clear programming operation completion flag
      \arg        EFUSE_RDIC: clear read operation completion flag
      \arg        EFUSE_OVBERIC: clear overstep boundary error flag
    \param[out] none
    \retval     none
*/
void efuse_flag_clear(efuse_clear_flag_enum flag)
{
    EFUSE_CS |= (uint32_t)flag;
}

/*!
    \brief      enable EFUSE interrupt
    \param[in]  source: specifies an interrupt to enbale
                one or more parameters can be selected which are shown as below:
      \arg        EFUSE_INTEN_PG: programming operation completion interrupt
      \arg        EFUSE_INTEN_RD: read operation completion interrupt
      \arg        EFUSE_INTEN_OVBER: overstep boundary error interrupt
    \param[out] none
    \retval     none
*/
void efuse_interrupt_enable(efuse_int_enum source)
{
    EFUSE_CS |= (uint32_t)source;
}

/*!
    \brief      disable EFUSE interrupt
    \param[in]  source: specifies an interrupt to disbale
                one or more parameters can be selected which are shown as below:
      \arg        EFUSE_INTEN_PG: programming operation completion interrupt
      \arg        EFUSE_INTEN_RD: read operation completion interrupt
      \arg        EFUSE_INTEN_OVBER: overstep boundary error interrupt
    \param[out] none
    \retval     none
*/
void efuse_interrupt_disable(efuse_int_enum source)
{
    EFUSE_CS &= (~(uint32_t)source);
}

/*!
    \brief      get EFUSE interrupt flag is set or not
    \param[in]  int_flag: specifies to get a flag
                only one parameter can be selected which is shown as below:
      \arg        EFUSE_INT_PGIF: programming operation completion interrupt flag
      \arg        EFUSE_INT_RDIF: read operation completion interrupt flag
      \arg        EFUSE_INT_OVBERIF: overstep boundary error interrupt flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus efuse_interrupt_flag_get(efuse_int_flag_enum int_flag)
{
    if(EFUSE_CS & (uint32_t)int_flag) {
        return SET;
    } else {
        return RESET;
    }
}

/*!
    \brief      clear EFUSE pending interrupt flag
    \param[in]  int_flag: specifies to clear a flag
                only one parameter can be selected which is shown as below:
      \arg        EFUSE_INT_PGIC: clear programming operation completion interrupt flag
      \arg        EFUSE_INT_RDIC: clear operation completion interrupt flag
      \arg        EFUSE_INT_OVBERIC: clear overstep boundary error interrupt flag
    \param[out] none
    \retval     none
*/
void efuse_interrupt_flag_clear(efuse_clear_int_flag_enum int_flag)
{
    EFUSE_CS |= ((uint32_t)int_flag);
}
