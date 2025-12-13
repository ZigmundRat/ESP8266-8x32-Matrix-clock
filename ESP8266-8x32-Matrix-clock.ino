/*
 * ESP8266 NTP Clock is written by John Rogers.
 * john@wizworks.net
 *
 * Permission for use is free to all, with the only condition that this notice is intact within
 * all copies or derivatives of this code. Improvements are welcome by pull request on the github
 * master repo.
 *
 * ESP8266 NTP Clock:  https://github.com/K1WIZ/ESP8266-8x32-Matrix-clock
 */

#include "Arduino.h"
#include <ESP8266WiFi.h>
#include <DNSServer.h>
#include <ESP8266WebServer.h>
#include <WiFiManager.h>
#include <ArduinoJson.h>
#include <EEPROM.h>
#include <NTPClient.h>
#include <WiFiUdp.h>
#include <time.h>

/* ================== MAX7219 PIN DEFINES (MUST BE BEFORE max7219.h) ================== */
#define NUM_MAX 4
#define DIN_PIN 13
#define CS_PIN  12
#define CLK_PIN 14

#include "max7219.h"
#include "fonts.h"

/* ================== CLOCK + DISPLAY STATE ================== */
#define MAX_DIGITS 16
byte dig[MAX_DIGITS]      = {0};
byte digold[MAX_DIGITS]   = {0};
byte digtrans[MAX_DIGITS] = {0};

bool is12HFormat = true;
bool isPM = false;
bool observeDST = false;

int updCnt = 0;
int dots = 0;
long dotTime = 0;
long clkTime = 0;
int dx = 0;
int dy = 0;
byte del = 0;

int h, m, s;
long epochUTC = 0;              // Always store UTC epoch here
long localMillisAtUpdate = 0;

int day, month, year, dayOfWeek;

/* ================== USER SETTINGS ================== */
float utcOffset = 0.0;         // hours, can be fractional
float dstExtraHours = 1.0;     // usually +1 hour

// Avoid DST_* symbol collisions with ESP8266 headers.
static const uint8_t CLOCK_DSTMODE_NONE = 0;
static const uint8_t CLOCK_DSTMODE_EU   = 1;
static const uint8_t CLOCK_DSTMODE_US   = 2;

// DEFAULT MUST BE US PER USER REQUEST:
uint8_t dstMode = CLOCK_DSTMODE_US;

/* Track whether portal actually saved settings (prevents overwriting EEPROM on reboot) */
volatile bool configWasSaved = false;

/* ================== WIFI + NTP ================== */
String clockHostname = "NTP-Clock";
WiFiManager wifiManager;

WiFiUDP ntpUDP;
NTPClient timeClient(ntpUDP, "pool.ntp.org", 0); // offset always 0 because we keep UTC

/* ================== EEPROM LAYOUT ================== */
struct Settings {
  float utcOffset;
  bool  observeDST;
  bool  is12H;
  uint8_t dstMode;
  float dstExtraHours;
  uint32_t magic;
};

static const uint32_t SETTINGS_MAGIC = 0x4B315749; // "K1WI"
static const int EEPROM_ADDR = 0;

Settings settings;

/* ================== WiFiManager Parameters ================== */
char bufUtc[12]      = "0";
char bufDst[6]       = "false";
char buf12h[6]       = "true";
char bufDstMode[10]  = "AUTO_US";  // DEFAULT MUST BE US
char bufDstExtra[12] = "1.0";

WiFiManagerParameter pUtc("utcoffset", "UTC Offset (hours, e.g. -5, +1, +5.5)", bufUtc, sizeof(bufUtc));
WiFiManagerParameter pDst("observedst", "Observe DST? (true/false)", bufDst, sizeof(bufDst));
WiFiManagerParameter p12h("is12h", "12 Hour Format? (true/false)", buf12h, sizeof(buf12h));
WiFiManagerParameter pDstMode("dstmode", "DST Mode: AUTO_US / AUTO_EU / NONE", bufDstMode, sizeof(bufDstMode));
WiFiManagerParameter pDstExtra("dstextra", "DST Extra Hours (usually 1.0)", bufDstExtra, sizeof(bufDstExtra));

/* ================== FORWARD DECLS ================== */
void saveConfigCallback();
void loadSettings();
void applySettingsToRuntime();
void writeSettingsFromRuntime();

long getTimeUTC();
void updateTime(long epochUTC, long localMillisAtUpdate);

bool isDST_EU_UTC(time_t utcNow);
bool isDST_US_Local(time_t utcNow, float baseUtcOffsetHours);

void setIntensity();
void showAnimClock();
void showDigit(char ch, int col, const uint8_t* data);
void setCol(int col, byte v);
int showChar(char ch, const uint8_t* data);
void printCharWithShift(unsigned char c, int shiftDelay);
void printStringWithShift(const char* s, int shiftDelay);

/* ================== DATE MATH (NO timegm) ================== */
// Day-of-week for Gregorian calendar. Returns 0=Sunday ... 6=Saturday.
static int dow_ymd(int y, int m, int d) {
  // Sakamoto's algorithm
  static int t[] = {0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4};
  if (m < 3) y -= 1;
  int dow = (y + y/4 - y/100 + y/400 + t[m-1] + d) % 7;
  return dow;
}

static bool isLeap(int y) {
  return ((y % 4 == 0 && y % 100 != 0) || (y % 400 == 0));
}

static int daysInMonth(int y, int m) {
  switch (m) {
    case 1: case 3: case 5: case 7: case 8: case 10: case 12: return 31;
    case 4: case 6: case 9: case 11: return 30;
    case 2: return isLeap(y) ? 29 : 28;
    default: return 30;
  }
}

static int lastSundayOfMonth(int y, int m) {
  int last = daysInMonth(y, m);
  int w = dow_ymd(y, m, last); // 0=Sun..6=Sat
  return last - w;             // step back to Sunday
}

static int firstSundayOfMonth(int y, int m) {
  int w = dow_ymd(y, m, 1);
  int delta = (7 - w) % 7;
  return 1 + delta;
}

static int secondSundayOfMonth(int y, int m) {
  return firstSundayOfMonth(y, m) + 7;
}

/* ================== EEPROM SETTINGS ================== */
void loadSettings() {
  EEPROM.get(EEPROM_ADDR, settings);

  if (settings.magic != SETTINGS_MAGIC ||
      isnan(settings.utcOffset) ||
      settings.dstExtraHours < 0.0 || settings.dstExtraHours > 3.0 ||
      settings.dstMode > 2) {

    // Defaults (US mode default requested)
    settings.utcOffset = 0.0;
    settings.observeDST = false;
    settings.is12H = true;
    settings.dstMode = CLOCK_DSTMODE_US;
    settings.dstExtraHours = 1.0;
    settings.magic = SETTINGS_MAGIC;

    EEPROM.put(EEPROM_ADDR, settings);
    EEPROM.commit();
  }

  // Pre-fill portal buffers from settings
  dtostrf(settings.utcOffset, 0, 2, bufUtc);
  strcpy(bufDst, settings.observeDST ? "true" : "false");
  strcpy(buf12h, settings.is12H ? "true" : "false");
  strcpy(bufDstMode,
         settings.dstMode == CLOCK_DSTMODE_US ? "AUTO_US" :
         (settings.dstMode == CLOCK_DSTMODE_EU ? "AUTO_EU" : "NONE"));
  dtostrf(settings.dstExtraHours, 0, 1, bufDstExtra);
}

void applySettingsToRuntime() {
  utcOffset = settings.utcOffset;
  observeDST = settings.observeDST;
  is12HFormat = settings.is12H;
  dstMode = settings.dstMode;
  dstExtraHours = settings.dstExtraHours;
}

void writeSettingsFromRuntime() {
  settings.utcOffset = utcOffset;
  settings.observeDST = observeDST;
  settings.is12H = is12HFormat;
  settings.dstMode = dstMode;
  settings.dstExtraHours = dstExtraHours;
  settings.magic = SETTINGS_MAGIC;

  EEPROM.put(EEPROM_ADDR, settings);
  EEPROM.commit();
}

/* ================== WIFI MANAGER SAVE ================== */
void saveConfigCallback() {
  // IMPORTANT: only set this flag when portal actually saves
  configWasSaved = true;

  utcOffset   = atof(pUtc.getValue());
  observeDST  = String(pDst.getValue()) == "true";
  is12HFormat = String(p12h.getValue()) == "true";
  dstExtraHours = atof(pDstExtra.getValue());

  String mode = String(pDstMode.getValue());
  mode.toUpperCase();
  if (mode == "AUTO_US") dstMode = CLOCK_DSTMODE_US;
  else if (mode == "AUTO_EU") dstMode = CLOCK_DSTMODE_EU;
  else dstMode = CLOCK_DSTMODE_NONE;

  writeSettingsFromRuntime();
}

/* ================== SETUP ================== */
void setup() {
  Serial.begin(115200);
  EEPROM.begin(sizeof(Settings));

  // Load EEPROM first, and apply to runtime so a reboot keeps settings
  loadSettings();
  applySettingsToRuntime();

  wifiManager.setSaveParamsCallback(saveConfigCallback);
  wifiManager.addParameter(&pUtc);
  wifiManager.addParameter(&pDst);
  wifiManager.addParameter(&p12h);
  wifiManager.addParameter(&pDstMode);
  wifiManager.addParameter(&pDstExtra);

  WiFi.mode(WIFI_STA);
  WiFi.hostname(clockHostname.c_str());

  initMAX7219();
  sendCmdAll(CMD_SHUTDOWN, 1);
  sendCmdAll(CMD_INTENSITY, 0);

  Serial.print("Connecting WiFi ");

  configWasSaved = false;

  if (!wifiManager.autoConnect("NTP Clock Setup")) {
    Serial.println("Failed to connect and hit timeout");
    delay(3000);
    ESP.restart();
    delay(5000);
  }

  // CRITICAL: do NOT overwrite EEPROM unless the callback fired
  if (configWasSaved) {
    Serial.println("Config saved via portal; EEPROM updated.");
  } else {
    Serial.println("Using stored EEPROM settings (portal not saved).");
    // Ensure runtime stays aligned to stored settings (not portal defaults)
    applySettingsToRuntime();
  }

  // Optional: show values
  Serial.println("");
  Serial.print("MyIP: ");
  Serial.println(WiFi.localIP());
  Serial.print("UTC Offset: ");
  Serial.println(utcOffset);
  Serial.print("Observe DST: ");
  Serial.println(observeDST ? "true" : "false");
  Serial.print("DST Mode: ");
  Serial.println(dstMode == CLOCK_DSTMODE_US ? "AUTO_US" : (dstMode == CLOCK_DSTMODE_EU ? "AUTO_EU" : "NONE"));
  Serial.print("DST Extra Hours: ");
  Serial.println(dstExtraHours);

  printStringWithShift("Connecting", 15);
  printStringWithShift((String("  MyIP: ") + WiFi.localIP().toString()).c_str(), 15);
  delay(1000);

  timeClient.begin();
  epochUTC = getTimeUTC();
}

/* ================== LOOP ================== */
void loop() {
  if (updCnt <= 0) {
    updCnt = 60;
    Serial.println("Getting data ...");
    printStringWithShift("   Setting Time...", 15);
    epochUTC = getTimeUTC();
    Serial.println("Data loaded");
    clkTime = millis();
  }

  if (millis() - clkTime > 20000 && !del && dots) {
    updCnt--;
    clkTime = millis();
  }

  if (millis() - dotTime > 500) {
    dotTime = millis();
    dots = !dots;
  }

  updateTime(epochUTC, localMillisAtUpdate);
  setIntensity();
  showAnimClock();
}

/* ================== NTP ================== */
long getTimeUTC() {
  timeClient.update();
  epochUTC = timeClient.getEpochTime();   // UTC only
  localMillisAtUpdate = millis();
  Serial.print("UTC epoch: ");
  Serial.println(epochUTC);
  return epochUTC;
}

/* ================== DST RULES ================== */
bool isDST_EU_UTC(time_t utcNow) {
  struct tm u;
  gmtime_r(&utcNow, &u);

  int y = u.tm_year + 1900;
  int mon = u.tm_mon + 1;
  int d = u.tm_mday;
  int hr = u.tm_hour;

  if (mon < 3 || mon > 10) return false;
  if (mon > 3 && mon < 10) return true;

  if (mon == 3) {
    int lastSun = lastSundayOfMonth(y, 3);
    if (d > lastSun) return true;
    if (d < lastSun) return false;
    return (hr >= 1); // starts 01:00 UTC
  }

  // mon == 10
  int lastSun = lastSundayOfMonth(y, 10);
  if (d < lastSun) return true;
  if (d > lastSun) return false;
  return (hr < 1); // ends 01:00 UTC
}

bool isDST_US_Local(time_t utcNow, float baseUtcOffsetHours) {
  // Convert UTC -> "local standard time" by applying base offset only (no DST)
  time_t localStd = utcNow + (long)(baseUtcOffsetHours * 3600);

  struct tm lt;
  gmtime_r(&localStd, &lt);

  int y = lt.tm_year + 1900;
  int mon = lt.tm_mon + 1;
  int d = lt.tm_mday;
  int hr = lt.tm_hour;

  if (mon < 3 || mon > 11) return false;
  if (mon > 3 && mon < 11) return true;

  if (mon == 3) {
    int startDay = secondSundayOfMonth(y, 3);
    if (d > startDay) return true;
    if (d < startDay) return false;
    return (hr >= 2); // starts 02:00 local
  }

  // mon == 11
  int endDay = firstSundayOfMonth(y, 11);
  if (d < endDay) return true;
  if (d > endDay) return false;
  return (hr < 2); // ends 02:00 local
}

/* ================== APPLY OFFSET + DST + UPDATE GLOBALS ================== */
void updateTime(long epochUtcAtSync, long millisAtSync) {
  time_t utcNow = (time_t)(epochUtcAtSync + (millis() - millisAtSync) / 1000);

  // apply base offset
  time_t local = utcNow + (long)(utcOffset * 3600);

  // apply DST if enabled
  if (observeDST && dstMode != CLOCK_DSTMODE_NONE) {
    bool dstNow = false;

    if (dstMode == CLOCK_DSTMODE_EU) {
      dstNow = isDST_EU_UTC(utcNow);
    } else if (dstMode == CLOCK_DSTMODE_US) {
      dstNow = isDST_US_Local(utcNow, utcOffset);
    }

    if (dstNow) {
      local += (long)(dstExtraHours * 3600);
    }
  }

  struct tm t;
  gmtime_r(&local, &t);

  h = t.tm_hour;
  m = t.tm_min;
  s = t.tm_sec;

  year  = t.tm_year + 1900;
  month = t.tm_mon + 1;
  day   = t.tm_mday;
  dayOfWeek = t.tm_wday;
}

/* ================== INTENSITY ================== */
void setIntensity() {
  int intensityHour = h;
  if (intensityHour >= 22 || intensityHour < 6) {
    sendCmdAll(CMD_INTENSITY, 0);
  } else if ((intensityHour >= 7 && intensityHour <= 10) || (intensityHour >= 16 && intensityHour < 18)) {
    sendCmdAll(CMD_INTENSITY, 3);
  } else if (intensityHour >= 11 && intensityHour <= 15) {
    sendCmdAll(CMD_INTENSITY, 5);
  } else if (intensityHour >= 19 && intensityHour <= 22) {
    sendCmdAll(CMD_INTENSITY, 2);
  }
}

/* ================== DISPLAY (YOUR ORIGINAL ANIMATION) ================== */
void showAnimClock() {
  byte digPos[6] = { 0, 8, 17, 25, 34, 42 };
  int digHt = 12;
  int num = 6;
  int i;

  if (del == 0) {
    del = digHt;
    for (i = 0; i < num; i++) digold[i] = dig[i];

    int displayHour = h;

    if (is12HFormat) {
      isPM = displayHour >= 12;
      displayHour %= 12;
      displayHour = displayHour ? displayHour : 12;
    }

    dig[0] = displayHour / 10 ? displayHour / 10 : (is12HFormat ? 10 : 0);
    dig[1] = displayHour % 10;
    dig[2] = m / 10;
    dig[3] = m % 10;
    dig[4] = s / 10;
    dig[5] = s % 10;

    for (i = 0; i < num; i++) digtrans[i] = (dig[i] == digold[i]) ? 0 : digHt;
  } else {
    del--;
  }

  clr();
  for (i = 0; i < num; i++) {
    if (digtrans[i] == 0) {
      dy = 0;
      showDigit(dig[i], digPos[i], dig6x8);
    } else {
      dy = 12 - digtrans[i];
      showDigit(digold[i], digPos[i], dig6x8);
      dy = -digtrans[i];
      showDigit(dig[i], digPos[i], dig6x8);
      digtrans[i]--;
    }
  }
  dy = 0;

  setCol(15, dots ? B00100100 : 0);
  setCol(32, dots ? B00100100 : 0);
  refreshAll();
  delay(30);
}

void showDigit(char ch, int col, const uint8_t* data) {
  if (dy < -8 || dy > 8) return;
  int len = pgm_read_byte(data);
  int w = pgm_read_byte(data + 1 + ch * len);
  col += dx;
  for (int i = 0; i < w; i++) {
    if (col + i >= 0 && col + i < 8 * NUM_MAX) {
      byte v = pgm_read_byte(data + 1 + ch * len + 1 + i);
      if (!dy) scr[col + i] = v;
      else scr[col + i] |= dy > 0 ? v >> dy : v << -dy;
    }
  }
}

void setCol(int col, byte v) {
  if (dy < -8 || dy > 8) return;
  col += dx;
  if (col >= 0 && col < 8 * NUM_MAX) {
    if (!dy) scr[col] = v;
    else scr[col] |= dy > 0 ? v >> dy : v << -dy;
  }
}

int showChar(char ch, const uint8_t* data) {
  int len = pgm_read_byte(data);
  int i, w = pgm_read_byte(data + 1 + ch * len);
  for (i = 0; i < w; i++)
    scr[NUM_MAX * 8 + i] = pgm_read_byte(data + 1 + ch * len + 1 + i);
  scr[NUM_MAX * 8 + i] = 0;
  return w;
}

void printCharWithShift(unsigned char c, int shiftDelay) {
  if (c < ' ' || c > '~' + 25) return;
  c -= 32;
  int w = showChar(c, font);
  for (int i = 0; i < w + 1; i++) {
    delay(shiftDelay);
    scrollLeft();
    refreshAll();
  }
}

void printStringWithShift(const char* s, int shiftDelay) {
  while (*s) {
    printCharWithShift(*s, shiftDelay);
    s++;
  }
}
