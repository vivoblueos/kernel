#include "cmsis_vstream.h"
#include "cmsis_os2.h"
#include "cmsis_compiler.h"

#include <stdio.h>
#include <string.h>

// Sensor characteristics
#define SENSOR_DATA_BYTES_PER_SAMPLE    (6U)

// Sensor data usage configuration
#define SENSOR_DATA_SAMPLES_PER_SLICE   (100U)

// Thread flag for signaling sensor data available
#define SENSOR_DATA_READY_FLAG          (1U)

// Raw sensor data sample structure
typedef struct {
  int16_t x;
  int16_t y;
  int16_t z;
} accelerometer_sample_t;

static uint8_t vstream_buf[(SENSOR_DATA_SAMPLES_PER_SLICE * SENSOR_DATA_BYTES_PER_SAMPLE) * 2] __ALIGNED(4);

// vStream driver
extern vStreamDriver_t     Driver_vStreamAccelerometer;
static vStreamDriver_t *ptrDriver_vStreamAccelerometer = &Driver_vStreamAccelerometer;

// Thread identifier
osThreadId_t threadId_threadDataProcess = NULL;

// Local function declaration
__NO_RETURN void threadDataProcess (void *argument);


// Function that signals thread event when data is available with vStream
static void vStreamEvent (uint32_t event_flags) {

  if ((event_flags & VSTREAM_EVENT_DATA) != 0U) {
    // Inform data processing thread that sensor data is available
    osThreadFlagsSet(threadId_threadDataProcess, SENSOR_DATA_READY_FLAG);
  }
}

// Function that initializes vStream for accelerometer
void vStreamInit (void) {

  ptrDriver_vStreamAccelerometer->Initialize(vStreamEvent);
  ptrDriver_vStreamAccelerometer->SetBuf(vstream_buf, sizeof(vstream_buf), SENSOR_DATA_SAMPLES_PER_SLICE * SENSOR_DATA_BYTES_PER_SAMPLE);
  ptrDriver_vStreamAccelerometer->Start(VSTREAM_MODE_CONTINUOUS);

  threadId_threadDataProcess = osThreadNew(threadDataProcess, NULL, NULL);
}

// Thread function that processes the sensor data
__NO_RETURN void threadDataProcess (void *argument) {
  accelerometer_sample_t *ptr_acc_sample;
  (void) argument;

  for (;;) {
    uint32_t flags = osThreadFlagsWait(SENSOR_DATA_READY_FLAG, osFlagsWaitAny, osWaitForever);

    if (((flags & osFlagsError)           == 0U) &&         // If not an error and
        ((flags & SENSOR_DATA_READY_FLAG) != 0U)) {         // if flag is sensor data ready

      // Get pointer to acquired sensor data
      ptr_acc_sample = (accelerometer_sample_t *)ptrDriver_vStreamAccelerometer->GetBlock();

      // Do something with sensor data, convert, copy for ML, ...
      // In this example we just print it to STDIO
      for (uint32_t i = 0U; i < SENSOR_DATA_SAMPLES_PER_SLICE; i++) {
        printf("Acc x=%i, y=%i, z=%i\r\n", ptr_acc_sample->x, ptr_acc_sample->y, ptr_acc_sample->z);
        ptr_acc_sample++;
      }
    }

    // Release current block for further data acquisition
    ptrDriver_vStreamAccelerometer->ReleaseBlock();
  }
}
