/*!
    \file    gd32vw55x_fmc.h
    \brief   definitions for the FMC

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

#include "gd32vw55x_fmc.h"

/* FMC mask */
/* FMC_OBR_SPC mask */
#define FMC_OBR_SPC_MASK                  ((uint32_t)0xFFFFFF00U)
/* FMC_OBUSER mask */
#define FMC_OBUSER_MASK                   ((uint32_t)0x00000000U)
/* FMC_OBSTAT security protection mask */
#define FMC_OBSTAT_SPCSTAT_MASK           ((uint32_t)0x00000002U)
/* FMC_OBWRPx/FMC_OFRG end page of region offset */
#define FMC_EPAGE_OFFSET                  ((uint32_t)16U)

/* return the FMC state */
static fmc_state_enum fmc_state_get(void);
/* check FMC ready or not */
static fmc_state_enum fmc_ready_wait(uint32_t timeout);

/*!
    \brief      unlock the main FMC operation
                it is better to used in pairs with fmc_lock
    \param[in]  none
    \param[out] none
    \retval     none
*/
void fmc_unlock(void)
{
    if(RESET != (FMC_CTL & FMC_CTL_LK)){
        /* write the FMC unlock key */
        FMC_KEY = UNLOCK_KEY0;
        FMC_KEY = UNLOCK_KEY1;
    }
}

/*!
    \brief      lock the main FMC operation
                it is better to used in pairs with fmc_unlock after an operation
    \param[in]  none
    \param[out] none
    \retval     none
*/
void fmc_lock(void)
{
    /* set the LK bit */
    FMC_CTL |= FMC_CTL_LK;
}

/*!
    \brief      FMC erase page
    \param[in]  page_address: target page address
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum fmc_page_erase(uint32_t page_address)
{
    fmc_state_enum fmc_state = FMC_READY;

    /* wait for the FMC ready */
    fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        /* start page erase */
        FMC_CTL |= FMC_CTL_PER;
        FMC_ADDR = page_address;
        FMC_CTL |= FMC_CTL_START;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
        /* reset the PER bit */
        FMC_CTL &= ~FMC_CTL_PER;
    }

    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      FMC erase whole chip
    \param[in]  none
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum fmc_mass_erase(void)
{
    fmc_state_enum fmc_state = FMC_READY;

    /* wait for the FMC ready */
    fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        /* start chip erase */
        FMC_CTL |= FMC_CTL_MER;
        FMC_CTL |= FMC_CTL_START;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
        /* reset the MER bit */
        FMC_CTL &= ~FMC_CTL_MER;
    }

    /* return the FMC state  */
    return fmc_state;
}

/*!
    \brief      FMC program a word at the corresponding address
    \param[in]  address: address to program
    \param[in]  data: word to program
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum fmc_word_program(uint32_t address, uint32_t data)
{
    fmc_state_enum fmc_state = FMC_READY;

    /* wait for the FMC ready */
    fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        /* set the PG bit to start program */
        FMC_CTL |= FMC_CTL_PG;
        REG32(address) = data;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
        /* reset the PG bit */
        FMC_CTL &= ~FMC_CTL_PG;
    }

    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      FMC program data continuously at the corresponding address
    \param[in]  address: address to program, must be 4-byte aligned
    \param[in]  data: data buffer to program
    \param[in]  size: data buffer size in bytes, must be 4-byte aligned
    \param[out] none
    \retval     state of FMC   
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum fmc_continuous_program(uint32_t address, uint32_t data[], uint32_t size)
{
    fmc_state_enum fmc_state = FMC_READY;

    /* wait for the FMC ready */
    fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        /* set the PG bit to start program */
        FMC_CTL |= FMC_CTL_PG;

        for(uint32_t i = 0U; i < size; i++){
            REG32(address) = data[i];
            address += 4U;
        }

        /* reset the PG bit */
        FMC_CTL &= ~FMC_CTL_PG;
    }

    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      enable FMC OBR function
    \param[in]  obr_function: the OBR function
                one or more parameters can be selected which are shown as below:
      \arg        FMC_OBR_NWDG_HW: watchdog status function
      \arg        FMC_OBR_NRST_STDBY: no reset generated when entering Standby mode function
      \arg        FMC_OBR_NSRT_DPSLP: no reset generated when entering DeepSleep mode function
      \arg        FMC_OBR_SRAM1_RST: SRAM1 reset automatically function
    \param[out] none
    \retval     none
*/
void fmc_obr_function_enable(uint32_t obr_function)
{
    FMC_OBR |= obr_function;
}

/*!
    \brief      disable FMC OBR function
    \param[in]  obr_function: the OBR function
                one or more parameters can be selected which are shown as below:
      \arg        FMC_OBR_NWDG_HW: watchdog status function
      \arg        FMC_OBR_NRST_STDBY: no reset generated when entering Standby mode function
      \arg        FMC_OBR_NSRT_DPSLP: no reset generated when entering DeepSleep mode function
      \arg        FMC_OBR_SRAM1_RST: SRAM1 reset automatically function
    \param[out] none
    \retval     none
*/
void fmc_obr_function_disable(uint32_t obr_function)
{
    FMC_OBR &= ~(uint32_t) obr_function;
}

/*!
    \brief      unlock the option bytes operation
    it is better to used in pairs with ob_lock
    \param[in]  none
    \param[out] none
    \retval     none
*/
void ob_unlock(void)
{
    if (RESET == (FMC_CTL & FMC_CTL_OBWEN)){
        /* write the FMC ob unlock key */
        FMC_OBKEY = UNLOCK_KEY0;
        FMC_OBKEY = UNLOCK_KEY1;
    }
}

/*!
    \brief      lock the option bytes operation
                it is better to used in pairs with ob_unlock after an operation
    \param[in]  none
    \param[out] none
    \retval     none
*/
void ob_lock(void)
{
    /* reset the OBWEN bit */
    FMC_CTL &= ~FMC_CTL_OBWEN;
}

/*!
    \brief      send option bytes modification start command
    \param[in]  none
    \param[out] none
    \retval     none
*/
void ob_start(void)
{
    /* set the OB_START bit in FMC_CTL register to start option bytes modification */
    FMC_CTL |= (FMC_CTL_OBSTART | FMC_CTL_OBWEN);
}

/*!
    \brief      reload option bytes
    \param[in]  none
    \param[out] none
    \retval     none
*/
void ob_reload(void)
{
    /* set the FMC_CTL_OBRLD bit in FMC_CTL register to reload option bytes */
    FMC_CTL |= FMC_CTL_OBRLD;
}

/*!
    \brief      configure security protection
                programmer must ensure FMC & option bytes are both unlocked before calling this function
    \param[in]  ob_spc: specify security protection
                only one parameter can be selected which is shown as below:
      \arg        FMC_NSPC: no security protection
      \arg        FMC_SPC_P1: security protection level 1
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum ob_security_protection_config(uint8_t ob_spc)
{
    fmc_state_enum fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        FMC_OBR &= FMC_OBR_SPC_MASK;
        FMC_OBR |= ob_spc;
        /* start option bytes modification */
        FMC_CTL |= FMC_CTL_OBSTART;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
    }

    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      program option bytes USER
                programmer must ensure FMC & option bytes are both unlocked before calling this function
    \param[in]  ob_user: option bytes user value
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum ob_user_write(uint32_t ob_user)
{
    fmc_state_enum fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        FMC_OBUSER &= FMC_OBUSER_MASK;
        FMC_OBUSER |= ob_user;
        /* start option bytes modification */
        FMC_CTL |= FMC_CTL_OBSTART;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
    }

    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      configure write protection pages
    \param[in]  wrp_spage: start page of write protection area, 0~0x3FF
    \param[in]  wrp_epage: end page of write protection area, 0~0x3FF
    \param[in]  wrp_register_index
                only one parameter can be selected which are shown as below:
      \arg        OBWRP_INDEX0: option byte write protection area register 0
      \arg        OBWRP_INDEX1: option byte write protection area register 1
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
fmc_state_enum ob_write_protection_config(uint32_t wrp_spage, uint32_t wrp_epage, uint32_t wrp_register_index)
{
    fmc_state_enum fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);

    if(FMC_READY == fmc_state){
        switch(wrp_register_index){
        case OBWRP_INDEX0:
            FMC_OBWRP0 = 0U;
            FMC_OBWRP0 |= wrp_spage;
            FMC_OBWRP0 |= wrp_epage << FMC_EPAGE_OFFSET;
            break;
        case OBWRP_INDEX1:
            FMC_OBWRP1 = 0U;
            FMC_OBWRP1 |= wrp_spage;
            FMC_OBWRP1 |= wrp_epage << FMC_EPAGE_OFFSET;
            break;
        default:
            break;
        }
        /* start option bytes modification */
        FMC_CTL |= FMC_CTL_OBSTART;
        /* wait for the FMC ready */
        fmc_state = fmc_ready_wait(FMC_TIMEOUT_COUNT);
    }
    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      configure NO-RTDEC pages
    \param[in]  nodec_spage: start page of NO-RTDEC area, 0~0x03FF
    \param[in]  nodec_epage: end page of NO-RTDEC area, 0~0x03FF
    \param[in]  nodec_register_index
                only one parameter can be selected which are shown as below:
      \arg        NODEC_INDEX0: NO-RTDEC region register 0
      \arg        NODEC_INDEX1: NO-RTDEC region register 1
      \arg        NODEC_INDEX2: NO-RTDEC region register 2
      \arg        NODEC_INDEX3: NO-RTDEC region register 3
    \param[out] none
    \retval     none
*/
void fmc_no_rtdec_config(uint32_t nodec_spage, uint32_t nodec_epage, uint32_t nodec_register_index)
{
    switch(nodec_register_index){
    case NODEC_INDEX0:
        FMC_NODEC0 = 0U;
        FMC_NODEC0 |= nodec_spage;
        FMC_NODEC0 |= nodec_epage << FMC_EPAGE_OFFSET;
        break;
    case NODEC_INDEX1:
        FMC_NODEC1 = 0U;
        FMC_NODEC1 |= nodec_spage;
        FMC_NODEC1 |= nodec_epage << FMC_EPAGE_OFFSET;
        break;
    case NODEC_INDEX2:
        FMC_NODEC2 = 0U;
        FMC_NODEC2 |= nodec_spage;
        FMC_NODEC2 |= nodec_epage << FMC_EPAGE_OFFSET;
        break;
    case NODEC_INDEX3:
        FMC_NODEC3 = 0U;
        FMC_NODEC3 |= nodec_spage;
        FMC_NODEC3 |= nodec_epage << FMC_EPAGE_OFFSET;
        break;
    default:
        break;
    }
}

/*!
    \brief      configure offset region
    \param[in]  of_spage: start page of offset region, 0~0x1FFF
    \param[in]  of_epage: end page of offset region, 0~0x1FFF
    \param[out] none
    \retval     none
*/
void fmc_offset_region_config(uint32_t of_spage, uint32_t of_epage)
{
    FMC_OFRG = 0U;
    FMC_OFRG |= (uint32_t) (of_spage);
    FMC_OFRG |= (uint32_t) (of_epage << FMC_EPAGE_OFFSET);
}

/*!
    \brief      configure offset value
    \param[in]  of_value: offset value, 0~0x1FFF
    \param[out] none
    \retval     none
*/
void fmc_offset_value_config(uint32_t of_value)
{
    FMC_OFVR = 0U;
    FMC_OFVR |= (uint32_t) (of_value);
}

/*!
    \brief      get calibration value
    \param[in]  none
    \param[out] rft0_bletxcal: BLE transmit power calibration value
    \param[out] rft0_wftxcal: WIFI transmit power calibration value
    \param[out] rft0_thecal: thermal meter calibration value
    \param[out] rft1_wfrxcal: WIFI receive gain calibration value
    \retval     none
*/
void fmc_wifi_trim_cal_get(uint32_t *rft0_bletxcal, uint32_t *rft0_wftxcal, uint32_t *rft0_thecal, uint32_t *rft1_wfrxcal)
{
    uint32_t rft0_reg;
    uint32_t rft1_reg;

    rft0_reg = FMC_RFT0;
    rft1_reg = FMC_RFT1;
    *rft0_bletxcal = (uint32_t)(rft0_reg & FMC_RFT0_BLETXCAL);
    *rft0_wftxcal = (uint32_t)(rft0_reg & FMC_RFT0_WIFITXCAL);
    *rft0_thecal = (uint32_t)(rft0_reg & FMC_RFT0_THECAL);
    *rft1_wfrxcal = (uint32_t)(rft1_reg & FMC_RFT1_WIFIRXGCAL);
}

/*!
    \brief      get Power Amplifier bias tune value
    \param[in]  none
    \param[out] rft0_pa_tune0: Power Amplifier bias coarse tune value
    \param[out] rft0_pa_tune1: Power Amplifier bias fine tune value
    \retval     none
*/
void fmc_wifi_trim_pa_get(uint32_t *rft0_pa_tune0, uint32_t *rft0_pa_tune1)
{
    uint32_t rft0_reg;

    rft0_reg = FMC_RFT0;
    *rft0_pa_tune0 = (uint32_t)(rft0_reg & FMC_RFT0_PABIAST0);
    *rft0_pa_tune1 = (uint32_t)(rft0_reg & FMC_RFT0_PABIAST1);
}

/*!
    \brief      get wifi trim
    \param[in]  size: the size of data written to wifi trim, must be 16U
    \param[in]  buf: the buffer of data read from wifi trim
    \param[out] none
    \retval     state of FMC
*/
fmc_state_enum fmc_wifi_trim_get(uint32_t size, uint32_t buf[])
{
    uint32_t i;

    if(size != 16U){
        return FMC_ERR;
    }
    for(i = 0; i < size; i++){
        buf[i] = REG32(FMC + 0x00000200U + i*4);
    }
    /* return the FMC state */
    return FMC_READY;
}

/*!
    \brief      get product ID
    \param[in]  none
    \param[out] pid: product ID
    \retval     none
*/
void fmc_pid_get(uint32_t *pid)
{
    uint32_t pid_addr = (uint32_t)pid;
    *(uint32_t *)pid_addr = (uint32_t)(FMC_PID0);
    pid_addr += 4U;
    *(uint32_t *)pid_addr = (uint32_t)(FMC_PID1);
}

/*!
    \brief      get option bytes write protection state, only applies to get the status of write/erase protection setting by EFUSE
    \param[in]  none
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus ob_write_protection_get(void)
{
    FlagStatus status = RESET;

    if(FMC_OBSTAT & FMC_OBSTAT_WP) {
        status = SET;
    } else {
        status = RESET;
    }

    /* return the state of corresponding FMC flag */
    return status;
}

/*!
    \brief      get the value of option bytes USER
    \param[in]  none
    \param[out] none
    \retval     the option bytes USER value
*/
uint32_t ob_user_get(void)
{
    /* return the FMC user option bytes value */
    return (uint32_t) FMC_OBUSER;
}

/*!
    \brief      get the FMC option bytes security protection state
    \param[in]  none
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus ob_security_protection_flag_get(void)
{
    FlagStatus state = RESET;

    if (FMC_OBSTAT & FMC_OBSTAT_SPCSTAT_MASK){
        state = SET;
    }else{
        state = RESET;
    }

    /* return the state of corresponding FMC flag */
    return state;
}

/*!
    \brief      get FMC flag status
    \param[in]  flag: FMC flag
                only one parameter can be selected which is shown as below:
      \arg        FMC_FLAG_BUSY: FMC busy flag
      \arg        FMC_FLAG_WPERR: FMC erase/program protection error flag
      \arg        FMC_FLAG_END: FMC end of operation flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus fmc_flag_get(uint32_t flag)
{
    FlagStatus status = RESET;

    if (FMC_STAT & flag){
        status = SET;
    }
    /* return the state of corresponding FMC flag */
    return status;
}

/*!
    \brief      clear the FMC flag
    \param[in]  flag: FMC flag
                only one parameter can be selected which is shown as below:
      \arg        FMC_FLAG_WPERR: FMC erase/program protection error flag
      \arg        FMC_FLAG_END: FMC end of operation flag
    \param[out] none
    \retval     none
*/
void fmc_flag_clear(uint32_t flag)
{
    /* clear the flags */
    FMC_STAT = flag;
}

/*!
    \brief      enable FMC interrupt
    \param[in]  interrupt: the FMC interrupt
                only one parameter can be selected which is shown as below:
      \arg        FMC_INT_END: FMC end of operation interrupt
      \arg        FMC_INT_ERR: FMC error interrupt
    \param[out] none
    \retval     none
*/
void fmc_interrupt_enable(uint32_t interrupt)
{
    FMC_CTL |= interrupt;
}

/*!
    \brief      disable FMC interrupt
    \param[in]  interrupt: the FMC interrupt
                only one parameter can be selected which is shown as below:
      \arg        FMC_INT_END: FMC end of operation interrupt
      \arg        FMC_INT_ERR: FMC error interrupt
    \param[out] none
    \retval     none
*/
void fmc_interrupt_disable(uint32_t interrupt)
{
    FMC_CTL &= ~(uint32_t) interrupt;
}

/*!
    \brief      get FMC interrupt flag
    \param[in]  flag: FMC interrupt flag
                only one parameter can be selected which is shown as below:
      \arg        FMC_INT_FLAG_WPERR: FMC erase/program protection error interrupt flag
      \arg        FMC_INT_FLAG_END: FMC end of operation interrupt flag
    \param[out] none
    \retval     FlagStatus: SET or RESET
*/
FlagStatus fmc_interrupt_flag_get(uint32_t flag)
{
    FlagStatus status = RESET;

    if(FMC_STAT & flag){
        status = SET;
    }
    /* return the state of corresponding FMC flag */
    return status;
}

/*!
    \brief      clear FMC interrupt flag
    \param[in]  flag: FMC interrupt flag
                only one parameter can be selected which is shown as below:
      \arg        FMC_INT_FLAG_WPERR: FMC erase/program protection error interrupt flag
      \arg        FMC_INT_FLAG_END: FMC end of operation interrupt flag
    \param[out] none
    \retval     none
*/
void fmc_interrupt_flag_clear(uint32_t flag)
{
    /* clear the flag */
    FMC_STAT = flag;
}

/*!
    \brief      get the FMC state
    \param[in]  none
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_BUSY: the operation is in progress
      \arg        FMC_WPERR: erase/program protection error
*/
static fmc_state_enum fmc_state_get(void)
{
    fmc_state_enum fmc_state = FMC_READY;

    if((uint32_t) 0x00U != (FMC_STAT & FMC_STAT_BUSY)){
        fmc_state = FMC_BUSY;
    }else{
        if((uint32_t) 0x00U != (FMC_STAT & FMC_STAT_WPERR)){
            fmc_state = FMC_WPERR;
        }
    }
    /* return the FMC state */
    return fmc_state;
}

/*!
    \brief      check whether FMC is ready or not
    \param[in]  timeout: timeout count
    \param[out] none
    \retval     state of FMC
      \arg        FMC_READY: the operation has been completed
      \arg        FMC_WPERR: erase/program protection error
      \arg        FMC_TOERR: timeout error
*/
static fmc_state_enum fmc_ready_wait(uint32_t timeout)
{
    fmc_state_enum fmc_state = FMC_BUSY;

    /* wait for FMC ready */
    do{
        /* get FMC state */
        fmc_state = fmc_state_get();
        timeout--;
    }while((FMC_BUSY == fmc_state) && (0x00U != timeout));

    if (FMC_BUSY == fmc_state){
        fmc_state = FMC_TOERR;
    }

    /* return the FMC state */
    return fmc_state;
}
