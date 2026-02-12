// Viene creato il gcode a partire da una immagine SVG. L'immagine è di 1000x700 pixel 
// viene creata una classe contenente anche il colore e la tipologia di forma (0=contorno, 1=filling)
// ogni shape (contorno o fill) viene inserita nella lista
// viene creata una nuova lista normalizzata alle dimensioni del foglio 
// crea una lista di sole linee a partire dalle shape
// viene creato il GCode a partire dalla lista normalizzata

import processing.embroider.*;
import geomerative.*;
import java.util.Locale;
import java.util.Date;  
import java.text.SimpleDateFormat; 
import java.util.Collections;
import java.util.Comparator;
// Aggiunti import per le classi del calcolatore di tempo
import java.util.*;
import java.util.regex.*;
import java.io.*;
import java.nio.file.*; // Potrebbe non essere strettamente necessario se si usa loadStrings

//Variabili del disegno
float step=1.5;
float stepDisplay; float stepSVG; //provarapp
boolean mixColors=false; //mescola i colori ogni tanto
boolean hatching=true; //ottieni i riempimenti a linee parallele
final int HATCH_FILL_PARALLEL = 0;
final int HATCH_FILL_CONCENTRIC = 1;
final int HATCH_FILL_SPIRAL = 2;
final int HATCH_FILL_PERLIN = 3;
final int HATCH_FILL_VECFIELD = 4;
int hatchFillMode = HATCH_FILL_PARALLEL;
boolean endStop=false;
//boolean border=true; //ottieni i bordi dell'immagine

//Dimensioni del foglio
//A3 395 260 0 50
//A4 285 205 0 35
//A3 Yupo 395 255 0 55
//max DIM Y = 650mm
int xDim=420;   //dimensione x della carta utile per dipingere
int yDim=297; //dimensione y della carta utile per dipingere
int xOffset=5; //offset x su carta
int yOffset=50; //offset y su carta
float rapp_carta=float(xDim)/float(yDim);
int xScreen=0;
int yScreen=0; //dimensione y dello screen
float xxMax=0;
int dimScreenMax=1000;

float distHatch=6; //distanza tra inizio e fine del tratteggio e il bordo
color colHide=#E3E4E6; //colore da non fare - FFFFFF = Bianco puro


///  variabili importanti per GCODE
float maxDist=35.0; //max lenght line painted - paper coordinate
float distMinLines=2; //min distance between lines without up the pen

///coordinate per GCODE
float absZDown=68.0;  //value Z when down paining
float radix=41.0+10.0;    //x base coordinate for first color
float radiy=0.0;  //y base coordinate for first color
float radiz=0.0;   //z base coordinate for first color
float absZUp=absZDown-30.0;  // value Z when up
float colZup=absZDown-66.0;   // value Z when up taking color
float colZDown=absZDown-30.0;  // value Z when down taking color
float watZUp=colZup;   //value Z when up taking water
//float watZdown=10.0; //value Z when down taking water
float watZdown=absZDown-30.0; //value Z when down taking water
float abszFront=33.0; //value A when painting
float abszBack=0.1;   //vale A when taking color
float spongeZup=0.0;      //value Z when up going on the sponge
float spongeZDown=0;    //value Z when down on the spongef

float add_x=41.0;   //x step for every color
float add_y=0.0;   //y step for every color

//float x_vaschetta=radix+8.5*add_x;   //x water
//float y_vaschetta=radiy+8.5*add_y; //y water
float x_vaschetta=10.0;   //x water
float y_vaschetta=0.0; //y water
float x_spugnetta=radix+10.0*add_x; //x sponge
float y_spugnetta=radiy+10.0*add_y; //x sponge
boolean spugnetta=false; //if need to dry the brush on the sponge

// velocità 
float speedAbs=1500.0;  //value of speed when painting
float speedFast=10000.0; // value of speed when traveling
float speedContour=1500.0; //value of speed painting the contours

boolean WriteFileLine=true; //scrivi anche il file con le linee e i valori delle linee 
boolean contour_white=false;  //contorno bianco delle figure 
float shRed=0.8; //riduzione della shape per avere il bianco intorno - non usato
String nomeAlgo="SVG"; //prefisso con cui vengono salvati i file
float angle; //angolo delle linee - da definire se lo vuoi fisso
float sovr; // larghezza righe in pixel
//float sovr=2; // larghezza righe in pixel

//color[] palette = {#ffff00, #800000, #00ffff, #ff0000, #ffffff, #ff00ff, #0000ff, #800080};
int numColori=1; //numero dei colori iniziale. Viene poi aumentato leggendo il file SVG
color[] palette = new color[numColori];

ArrayList<Forma> formaList = new ArrayList<Forma>();
ArrayList<Forma> paperFormList = new ArrayList<Forma>();
ArrayList<Linea> lineaList = new ArrayList<Linea>();
PEmbroiderGraphics E;
ArrayList<cBrigh> brighCol = new ArrayList<cBrigh>(); 

float factor;
PVector pos = new PVector(0, 0);  
String buf="";
PrintWriter OUTPUT, linee; 
String outFile=null; // Reso globale per essere accessibile dalla funzione di stima
// Variabili globali
int indiceInizio = 0;    // Indice di inizio del gruppo corrente
int indiceFine = 0;      // Indice che tiene traccia di quanto avanti siamo arrivati

/////////////////////
// Variabili disegno corrente
String nomeFile="";
String imgPath, path, fileN, fileNoExt;
PrintWriter reordFile; 

RShape img;
ArrayList ve;
int nve = 1;
int colo;
ArrayList<RShape> LShape=new ArrayList<RShape>();
IntList colori=new IntList();
IntList colSVG=new IntList();
int contaColSVG=0;
int conta=0;
int contaShape=0;
boolean primoColore=true;
float screenScaleFactor=0;
long durata=0;

ArrayList<RShape> bezier = new ArrayList<RShape>();

// Variabili globali per la stima del tempo G-code (aggiunte da claude.txt)
RussolinoMachineParams machineParams;
RussolinoTimeEstimator estimator;

final int UI_TOP = 84;
final int UI_BTN_W = 180;
final int UI_BTN_H = 44;
boolean gcodeExported = false;

final int UI_DD_W = 230;
final int UI_DD_H = 44;
final int UI_DD_ITEM_H = 34;
final int UI_GO_W = 64;
final int UI_GO_H = 44;
final int UI_PAPER_W = 230;
final int UI_FIELD_H = 44;
final int UI_FIELD_W = 88;
final int UI_PAD = 16;
final int UI_GAP = 10;
final int FIELD_NONE = 0;
final int FIELD_CUSTOM_W = 1;
final int FIELD_CUSTOM_H = 2;
final int FIELD_OFFSET_X = 3;
final int FIELD_OFFSET_Y = 4;

String[] hatchStyleLabels = { "PARALLEL", "CONCENTRIC", "SPIRAL", "PERLIN", "VECFIELD" };
int[] hatchStyleModes = { HATCH_FILL_PARALLEL, HATCH_FILL_CONCENTRIC, HATCH_FILL_SPIRAL, HATCH_FILL_PERLIN, HATCH_FILL_VECFIELD };
int hatchStyleSelectedIndex = 0;
int hatchStyleAppliedIndex = 0;
boolean hatchDropdownOpen = false;
boolean hasElaboration = false;
volatile boolean isElaborating = false;

String[] paperFormatLabels = { "A4 Verticale", "A4 Orizzontale", "A3 Verticale", "A3 Orizzontale", "Personalizzato" };
int[] paperFormatW = { 210, 297, 297, 420, -1 };
int[] paperFormatH = { 297, 210, 420, 297, -1 };
int paperFormatSelectedIndex = 3;
int paperFormatAppliedIndex = 3;
boolean paperDropdownOpen = false;

String paperCustomWText = str(xDim);
String paperCustomHText = str(yDim);
String offsetXText = str(xOffset);
String offsetYText = str(yOffset);
int activeField = FIELD_NONE;


/////////////////////////
void settings() {
  
  if (rapp_carta >= 1) {
    xScreen=dimScreenMax; //dimensioni x dello screen
    yScreen=int(dimScreenMax/rapp_carta); //dimensione y dello screen
  } else {
    yScreen=dimScreenMax;
    xScreen=int(dimScreenMax*rapp_carta);
  }
  
  size(xScreen*2, yScreen+100+UI_TOP);
  pixelDensity(1);
  Locale.setDefault(Locale.US);
}

//////////////////////////////////////////////////////////////////////////
void setup() {
  windowResize(xScreen*2, yScreen+100+UI_TOP);
  RG.init(this);
  
  E = new PEmbroiderGraphics(this, width, height);
   // PLOTTER-SPECIFIC COMMANDS: 
   // Set this to false so that there aren't superfluous waypoints on straight lines: 
   E.toggleResample(false); 
   // Set this to false so that there aren't connecting lines between shapes. 
   // Note that you'll still be able to pre-visualize the connecting lines 
   // (the plotter path) if you set E.visualize(true, true, true); 
   E.toggleConnectingLines(false); 
   // This affects the visual quality of inset/offset curves for CONCENTRIC fills: 
   E.CONCENTRIC_ANTIALIGN = 0.0;

  durata=millis();

  // Inizializza i parametri della macchina e lo stimatore del tempo
  machineParams = new RussolinoMachineParams();
  estimator = new RussolinoTimeEstimator(machineParams, this); // Passa 'this' per accedere a loadStrings()

  selectInput("Please select canvas picture:", "selectImage");
  while (img == null)  delay(100);
  background(255, 255, 255);
  
  println("*******************************************************************");
  int imageHeight=int(img.getHeight());
  int imageWidth=int(img.getWidth());
  println("Original SVG x size:"+imageWidth);
  println("Original SVG y size:"+imageHeight);

  float scaleImgX=0;
  float scaleImgY=0;
  if (rapp_carta >1) {
    scaleImgX = float(xScreen) / img.getWidth();
    img.scale(scaleImgX);
     if (img.getHeight() > yScreen) {
      scaleImgY = float(yScreen) / img.getHeight();
      img.scale(scaleImgY);
    }
  }
   else {
    scaleImgY = float(yScreen) / img.getWidth();
    img.scale(scaleImgY);
    if (img.getWidth() > xScreen) {
      scaleImgX = float(xScreen) / img.getWidth();
      img.scale(scaleImgX);
    }
   }
  println("Screen X :"+xScreen);
  println("Screen Y :"+yScreen);
  
  imageHeight=int(img.getHeight());
  imageWidth=int(img.getWidth());
  println("New SVG x size:"+imageWidth);
  println("New SVG y size:"+imageHeight);

  // Calculate aspect ratio of the image
  float imageAspectRatio = (float) imageWidth / imageHeight;
  println("Image Aspect Ratio: " + imageAspectRatio);

  // Determine which dimension (X or Y) of the image is the maximum
  boolean isXMax = imageWidth >= imageHeight;
  println("Is X dimension of the image maximum? " + isXMax);
  // Determine the maximum dimension based on the screen size
 
  float maxDimension = isXMax ? xScreen : yScreen;
  println("Maximum Dimension: " + maxDimension);

  // Calculate scaling factor for mapping to screen dimensions
  screenScaleFactor = maxDimension / (isXMax ? imageWidth : imageHeight);
  println("Screen Scale Factor: " + screenScaleFactor);

  // Map the dimensions to screen size
  float printedScreenWidth = imageWidth * screenScaleFactor;
  float printedScreenHeight = imageHeight * screenScaleFactor;
  println("Printed Screen Width: " + printedScreenWidth);
  println("Printed Screen Height: " + printedScreenHeight);

  // Calculate scaling factor for mapping to paper dimensions
  float paperWidthScaleFactor = float(xDim) / float(imageWidth);
  float paperHeightScaleFactor = float(yDim) / float(imageHeight);
  
  println("Paper Width Scale Factor: " + paperWidthScaleFactor);
  println("Paper Height Scale Factor: " + paperHeightScaleFactor);
  
  // Choose the smaller scale factor to ensure the image fits within both screen and paper
  float scaleFactor = min(screenScaleFactor, min(paperWidthScaleFactor, paperHeightScaleFactor));
  println("Chosen Scale Factor: " + scaleFactor);
  
  // Map the dimensions to paper size
  float printedPaperWidth = imageWidth * scaleFactor;
  float printedPaperHeight = imageHeight * scaleFactor;
  println("Printed Paper Width: " + printedPaperWidth);
  println("Printed Paper Height: " + printedPaperHeight);
 
  // Calculate reduction factor between screen dimensions and paper dimensions
  float reductionFactorWidth =  printedPaperWidth / printedScreenWidth;
  float reductionFactorHeight = printedPaperHeight / printedScreenHeight;
  println("Reduction Factor Width: " + reductionFactorWidth);
  println("Reduction Factor Height: " + reductionFactorHeight);

  //factor=reductionFactorWidth*screenScaleFactor;
  factor=scaleFactor;
  println("Redction factor paper vs screen:"+factor);

  stepDisplay=step/factor;
  stepSVG=stepDisplay;
  sovr=stepDisplay-0.5;
  print("Step paper:"+step); 
  print(" - Step display:"+stepDisplay);
  print(" - StepSVG:" + stepSVG);
  println(" - sovr:"+sovr);
    
 // yOffset=yOffset-int(printedPaperHeight);
 // xOffset=xOffset-int(printedPaperWidth);
  
  println("*******************************************************************");
  hatchStyleSelectedIndex = hatchIndexForMode(hatchFillMode);
  hatchStyleAppliedIndex = hatchStyleSelectedIndex;
  interactiveViewerEnabled = false;
  hasElaboration = false;
}

void applyPaperSettingsFromUI() {
  int nextXDim = xDim;
  int nextYDim = yDim;
  if (paperFormatSelectedIndex >= 0 && paperFormatSelectedIndex < paperFormatLabels.length) {
    if (paperFormatSelectedIndex == paperFormatLabels.length - 1) {
      Integer cw = parsePositiveIntOrNull(paperCustomWText);
      Integer ch = parsePositiveIntOrNull(paperCustomHText);
      if (cw != null && ch != null) {
        nextXDim = cw;
        nextYDim = ch;
      }
    } else {
      nextXDim = paperFormatW[paperFormatSelectedIndex];
      nextYDim = paperFormatH[paperFormatSelectedIndex];
    }
  }

  Integer ox = parseIntOrNull(offsetXText);
  Integer oy = parseIntOrNull(offsetYText);
  if (ox != null) xOffset = ox;
  if (oy != null) yOffset = oy;

  xDim = nextXDim;
  yDim = nextYDim;
  rapp_carta = float(xDim) / float(yDim);

  paperFormatAppliedIndex = paperFormatSelectedIndex;
  recomputePaperScaling();
}

void recomputePaperScaling() {
  if (img == null) return;
  int imageHeight = int(img.getHeight());
  int imageWidth = int(img.getWidth());
  if (imageWidth <= 0 || imageHeight <= 0) return;

  float paperWidthScaleFactor = float(xDim) / float(imageWidth);
  float paperHeightScaleFactor = float(yDim) / float(imageHeight);
  float scaleFactor = min(screenScaleFactor, min(paperWidthScaleFactor, paperHeightScaleFactor));
  factor = scaleFactor;
  stepDisplay = step / factor;
  stepSVG = stepDisplay;
  sovr = stepDisplay - 1;
}

Integer parsePositiveIntOrNull(String v) {
  Integer n = parseIntOrNull(v);
  if (n == null) return null;
  if (n <= 0) return null;
  return n;
}

Integer parseIntOrNull(String v) {
  if (v == null) return null;
  String s = trim(v);
  if (s == null || s.length() == 0) return null;
  try {
    return Integer.parseInt(s);
  } 
  catch (Exception e) {
    return null;
  }
}

int hatchIndexForMode(int mode) {
  for (int i = 0; i < hatchStyleModes.length; i++) {
    if (hatchStyleModes[i] == mode) return i;
  }
  return 0;
}

void buildHatchingAndViewer() {
  gcodeExported = false;
  hatchDropdownOpen = false;
  interactiveViewerEnabled = false;
  hasElaboration = false;

  indiceInizio = 0;
  indiceFine = 0;

  formaList.clear();
  paperFormList.clear();
  lineaList.clear();
  brighCol.clear();

  if (bezier != null) bezier.clear();
  ve = new ArrayList();
  colori.clear();
  colSVG.clear();
  contaColSVG = 0;
  primoColore = true;
  palette = new color[numColori];

  RG.setPolygonizer(RG.ADAPTATIVE);
  color fil = img.getStyle().fillColor;
  exVert(img, fil);

  for (int p = 0; p < bezier.size(); p++) {
    RShape curr = bezier.get(p);
    int colForm = curr.getStyle().fillColor;
    if (colForm == #FFFFFF) {
      bezier.remove(p);
      p--;
      continue;
    }

    int ic = -1;
    for (int i = 0; i < palette.length; i++) {
      if (palette[i] == colForm) {
        ic = i;
        i = palette.length;
      }
    }

    if (hatching) {
      intersection(curr, ic, distHatch / factor);
    }

    RShape currResize = curr;
    RPoint originalCenter = curr.getCenter();
    RPoint[] sb = currResize.getBoundsPoints();
    RShape Rsb = RShape.createRectangle(sb[0].x, sb[0].y, sb[1].x - sb[0].x, sb[2].y - sb[1].y);
    boolean isRsbMax = Rsb.getWidth() >= Rsb.getHeight();
    float maxRsb = isRsbMax ? Rsb.getWidth() : Rsb.getHeight();
    float factorCurrResize = stepSVG / maxRsb;
    currResize.scale(1.0 - factorCurrResize);
    RPoint newCenter = curr.getCenter();
    float dx = originalCenter.x - newCenter.x;
    float dy = originalCenter.y - newCenter.y;
    currResize.translate(dx, dy);
    formaList.add(new Forma(currResize, ic, 0));
  }

  paperFormList.clear();
  ridimPaper();

  lineaList.clear();
  creaLista();
  if (lineaList.size() > 0) {
    orderList();
    if (mixColors) mixColor();
    orderBrigh();
  }

  interactiveViewerInit();
  hasElaboration = true;
}

void runElaboration() {
  isElaborating = true;
  interactiveViewerEnabled = false;
  gcodeExported = false;
  hatchDropdownOpen = false;
  try {
    buildHatchingAndViewer();
  } 
  finally {
    isElaborating = false;
  }
}


void draw() {
  background(255);
  pushMatrix();
  translate(0, UI_TOP);
  disegnaOriginale(0);
  if (interactiveViewerEnabled) {
    interactiveViewerDrawAt(xScreen);
    disegnaBlocchetti(xScreen);
  }
  popMatrix();
  drawHatchControls();
  drawGcodeButton();
  drawElaborationOverlay();
}

void drawElaborationOverlay() {
  if (!isElaborating) return;
  noStroke();
  fill(255, 255, 255, 220);
  rect(0, UI_TOP, width, height - UI_TOP);
  fill(0);
  textAlign(CENTER, CENTER);
  textSize(32);
  text("ELABORATION...", width * 0.5, UI_TOP + (height - UI_TOP) * 0.5);
}

void drawHatchControls() {
  float ddY = UI_PAD;
  float ddX = UI_PAD;
  boolean overHatchDd = mouseX >= ddX && mouseX <= ddX + UI_DD_W && mouseY >= ddY && mouseY <= ddY + UI_DD_H;
  stroke(0);
  if (overHatchDd) fill(245);
  else fill(235);
  rect(ddX, ddY, UI_DD_W, UI_DD_H, 8);

  fill(0);
  textAlign(LEFT, CENTER);
  textSize(16);
  text("HATCHING " + hatchStyleLabels[hatchStyleSelectedIndex], ddX + 12, ddY + UI_DD_H * 0.5);

  float goX = ddX + UI_DD_W + UI_GAP;
  float goY = ddY;
  boolean overGo = mouseX >= goX && mouseX <= goX + UI_GO_W && mouseY >= goY && mouseY <= goY + UI_GO_H;
  stroke(0);
  if (overGo) fill(80, 150, 255);
  else fill(40, 120, 255);
  rect(goX, goY, UI_GO_W, UI_GO_H, 8);
  fill(255);
  textAlign(CENTER, CENTER);
  textSize(18);
  text("GO", goX + UI_GO_W * 0.5, goY + UI_GO_H * 0.5);

  float paperX = goX + UI_GO_W + 100;
  float paperY = ddY;
  boolean overPaperDd = mouseX >= paperX && mouseX <= paperX + UI_PAPER_W && mouseY >= paperY && mouseY <= paperY + UI_DD_H;
  stroke(0);
  if (overPaperDd) fill(245);
  else fill(235);
  rect(paperX, paperY, UI_PAPER_W, UI_DD_H, 8);

  fill(0);
  textAlign(LEFT, CENTER);
  textSize(16);
  text("TIPO " + paperFormatLabels[paperFormatSelectedIndex], paperX + 12, paperY + UI_DD_H * 0.5);

  float fieldsY = ddY;
  float fieldsX = paperX + UI_PAPER_W + UI_GAP;
  boolean customEnabled = (paperFormatSelectedIndex == paperFormatLabels.length - 1);
  drawCompactField(fieldsX, fieldsY, "W", paperCustomWText, FIELD_CUSTOM_W, customEnabled);
  drawCompactField(fieldsX + UI_FIELD_W + UI_GAP, fieldsY, "H", paperCustomHText, FIELD_CUSTOM_H, customEnabled);
  drawCompactField(fieldsX + (UI_FIELD_W + UI_GAP) * 2, fieldsY, "OX", offsetXText, FIELD_OFFSET_X, true);
  drawCompactField(fieldsX + (UI_FIELD_W + UI_GAP) * 3, fieldsY, "OY", offsetYText, FIELD_OFFSET_Y, true);

  if (hatchDropdownOpen) {
    float listX = ddX;
    float listY = ddY + UI_DD_H + 6;
    for (int i = 0; i < hatchStyleLabels.length; i++) {
      stroke(0);
      fill(255);
      rect(listX, listY + i * UI_DD_ITEM_H, UI_DD_W, UI_DD_ITEM_H);
      fill(0);
      textAlign(LEFT, CENTER);
      textSize(14);
      text(hatchStyleLabels[i], listX + 12, listY + i * UI_DD_ITEM_H + UI_DD_ITEM_H * 0.5);
    }
  }

  if (paperDropdownOpen) {
    float listX = paperX;
    float listY = paperY + UI_DD_H + 6;
    for (int i = 0; i < paperFormatLabels.length; i++) {
      stroke(0);
      fill(255);
      rect(listX, listY + i * UI_DD_ITEM_H, UI_PAPER_W, UI_DD_ITEM_H);
      fill(0);
      textAlign(LEFT, CENTER);
      textSize(14);
      text(paperFormatLabels[i], listX + 12, listY + i * UI_DD_ITEM_H + UI_DD_ITEM_H * 0.5);
    }
  }
}

void drawCompactField(float x, float y, String label, String value, int fieldId, boolean enabled) {
  boolean active = (activeField == fieldId);
  boolean over = mouseX >= x && mouseX <= x + UI_FIELD_W && mouseY >= y && mouseY <= y + UI_FIELD_H;
  stroke(0);
  if (!enabled) fill(220);
  else if (active) fill(255, 245, 140);
  else if (over) fill(245);
  else fill(235);
  rect(x, y, UI_FIELD_W, UI_FIELD_H, 8);
  fill(enabled ? 0 : 120);
  textAlign(CENTER, CENTER);
  textSize(14);
  String shown = value != null && value.length() > 0 ? (label + " " + value) : label;
  text(shown, x + UI_FIELD_W * 0.5, y + UI_FIELD_H * 0.5);
}

void drawGcodeButton() {
  float y = UI_PAD;
  float ddX = UI_PAD;
  float goX = ddX + UI_DD_W + UI_GAP;
  float paperX = goX + UI_GO_W + 100;
  float fieldsX = paperX + UI_PAPER_W + UI_GAP;
  float desiredX = fieldsX + (UI_FIELD_W + UI_GAP) * 4 + 100;
  float x = min(width - UI_PAD - UI_BTN_W, desiredX);
  boolean over = mouseX >= x && mouseX <= x + UI_BTN_W && mouseY >= y && mouseY <= y + UI_BTN_H;

  stroke(0);
  if (!interactiveViewerEnabled) fill(120, 170, 255);
  else if (over) fill(80, 150, 255);
  else fill(40, 120, 255);
  rect(x, y, UI_BTN_W, UI_BTN_H, 8);

  fill(255);
  textAlign(CENTER, CENTER);
  textSize(20);
  text("GCODE", x + UI_BTN_W * 0.5, y + UI_BTN_H * 0.5);
}

void mousePressed() {
  if (isElaborating) return;
  float ddY = UI_PAD;
  float ddX = UI_PAD;
  float goX = ddX + UI_DD_W + UI_GAP;
  float goY = ddY;
  float paperX = goX + UI_GO_W + 100;
  float paperY = ddY;
  float fieldsX = paperX + UI_PAPER_W + UI_GAP;
  float desiredGcodeX = fieldsX + (UI_FIELD_W + UI_GAP) * 4 + 100;
  float gcodeX = min(width - UI_PAD - UI_BTN_W, desiredGcodeX);
  float gcodeY = UI_PAD;

  boolean onDropdown = mouseX >= ddX && mouseX <= ddX + UI_DD_W && mouseY >= ddY && mouseY <= ddY + UI_DD_H;
  if (onDropdown) {
    hatchDropdownOpen = !hatchDropdownOpen;
    paperDropdownOpen = false;
    activeField = FIELD_NONE;
    redraw();
    return;
  }

  if (hatchDropdownOpen) {
    float listX = ddX;
    float listY = ddY + UI_DD_H + 6;
    boolean picked = false;
    for (int i = 0; i < hatchStyleLabels.length; i++) {
      float iy = listY + i * UI_DD_ITEM_H;
      if (mouseX >= listX && mouseX <= listX + UI_DD_W && mouseY >= iy && mouseY <= iy + UI_DD_ITEM_H) {
        hatchStyleSelectedIndex = i;
        hatchDropdownOpen = false;
        picked = true;
        break;
      }
    }
    if (!picked) hatchDropdownOpen = false;
    redraw();
    return;
  }

  boolean onPaperDropdown = mouseX >= paperX && mouseX <= paperX + UI_PAPER_W && mouseY >= paperY && mouseY <= paperY + UI_DD_H;
  if (onPaperDropdown) {
    paperDropdownOpen = !paperDropdownOpen;
    hatchDropdownOpen = false;
    activeField = FIELD_NONE;
    redraw();
    return;
  }

  if (paperDropdownOpen) {
    float listX = paperX;
    float listY = paperY + UI_DD_H + 6;
    boolean picked = false;
    for (int i = 0; i < paperFormatLabels.length; i++) {
      float iy = listY + i * UI_DD_ITEM_H;
      if (mouseX >= listX && mouseX <= listX + UI_PAPER_W && mouseY >= iy && mouseY <= iy + UI_DD_ITEM_H) {
        paperFormatSelectedIndex = i;
        if (paperFormatSelectedIndex >= 0 && paperFormatSelectedIndex < paperFormatLabels.length - 1) {
          paperCustomWText = str(paperFormatW[paperFormatSelectedIndex]);
          paperCustomHText = str(paperFormatH[paperFormatSelectedIndex]);
        }
        paperDropdownOpen = false;
        picked = true;
        break;
      }
    }
    if (!picked) paperDropdownOpen = false;
    redraw();
    return;
  }

  float fieldsY = ddY;
  boolean customEnabled = (paperFormatSelectedIndex == paperFormatLabels.length - 1);
  if (tryActivateField(fieldsX, fieldsY, FIELD_CUSTOM_W, customEnabled)) return;
  if (tryActivateField(fieldsX + UI_FIELD_W + UI_GAP, fieldsY, FIELD_CUSTOM_H, customEnabled)) return;
  if (tryActivateField(fieldsX + (UI_FIELD_W + UI_GAP) * 2, fieldsY, FIELD_OFFSET_X, true)) return;
  if (tryActivateField(fieldsX + (UI_FIELD_W + UI_GAP) * 3, fieldsY, FIELD_OFFSET_Y, true)) return;

  boolean onGo = mouseX >= goX && mouseX <= goX + UI_GO_W && mouseY >= goY && mouseY <= goY + UI_GO_H;
  if (onGo) {
    hatchFillMode = hatchStyleModes[hatchStyleSelectedIndex];
    hatchStyleAppliedIndex = hatchStyleSelectedIndex;
    applyPaperSettingsFromUI();
    thread("runElaboration");
    return;
  }

  boolean onGcode = mouseX >= gcodeX && mouseX <= gcodeX + UI_BTN_W && mouseY >= gcodeY && mouseY <= gcodeY + UI_BTN_H;
  if (onGcode) {
    if (interactiveViewerEnabled && !gcodeExported) exportOutputs();
    redraw();
  }

  activeField = FIELD_NONE;
}

boolean tryActivateField(float fieldX, float fieldY, int fieldId, boolean enabled) {
  if (!enabled) return false;
  if (mouseX < fieldX || mouseX > fieldX + UI_FIELD_W) return false;
  if (mouseY < fieldY || mouseY > fieldY + UI_FIELD_H) return false;
  if (activeField != fieldId) {
    if (fieldId == FIELD_CUSTOM_W) paperCustomWText = "";
    else if (fieldId == FIELD_CUSTOM_H) paperCustomHText = "";
    else if (fieldId == FIELD_OFFSET_X) offsetXText = "";
    else if (fieldId == FIELD_OFFSET_Y) offsetYText = "";
  }
  activeField = fieldId;
  redraw();
  return true;
}

void exportOutputs() {
  if (path == null || path.isEmpty() || fileNoExt == null || fileNoExt.isEmpty()) return;

  File outDir = new File(path, "GCODE");
  if (!outDir.exists()) outDir.mkdirs();

  outFile = outDir.getAbsolutePath() + "/" + fileNoExt + ".GCODE";
  String lineeFile = outDir.getAbsolutePath() + "/" + fileNoExt + ".txt";

  OUTPUT = createWriter(outFile);
  linee = createWriter(lineeFile);

  linee.println("Dimensioni foglio:"+xDim+"x"+yDim);
  linee.println("Offset:"+xOffset+"x"+yOffset+"\n");
  linee.println("Numero di shape:"+formaList.size());
  linee.println("Numero di linee:"+lineaList.size());

  Glines = 0;
  max_gcode_x = 0;
  max_gcode_y = 0;
  min_gcode_x = 10000;
  min_gcode_y = 10000;
  zFront = false;
  is_pen_down = false;
  pos.set(0, 0);

  creaGCODE();

  linee.println("GCode Lines:"+Glines);
  linee.print("Min Gcode x:"+min_gcode_x);
  linee.println("  Max Gcode x:"+max_gcode_x);
  linee.print("Min Gcode y:"+min_gcode_y);
  linee.println("  Max Gcode y:"+max_gcode_y+"\n\n");
  scriviLineeFile();

  pen_color_up();
  String buf = "G0 Z0";
  OUTPUT.println(buf);
  Glines++;
  buf = "G1 X0 Y0 F6000";
  OUTPUT.println(buf);
  Glines++;
  buf = "G0 A0";
  OUTPUT.println(buf);
  Glines++;

  linee.flush();
  linee.close();

  OUTPUT.flush();
  OUTPUT.close();

  PImage shot = get(xScreen, UI_TOP, xScreen, yScreen+100);
  shot.save(outDir.getAbsolutePath() + "/" + fileNoExt + "-screen.png");

  calculateGCodeTime();
  gcodeExported = true;
}


////////////////////////////////////////////////
void selectImage(final File f) {
  if (f == null || f.isDirectory()) {
    println("Window was closed or you've hit cancel.\n");
    System.exit(0);
  }
  
  // Verifica se il file selezionato è un file SVG
  String fileName = f.getName().toLowerCase();
  if (!fileName.endsWith(".svg")) {
    println("Please select a SVG file (.svg extension)");
    selectInput("Please select a SVG file:", "selectImage");
    return;
  }
  
  imgPath = f.getPath();
  println("Img Path: "+imgPath);
  path = f.getParent() + "/";
  fileN = f.getName();
  println("Input Path: "+path);
  fileNoExt = fileN.substring(0, fileN.length()-4);
  println("******************************************************");
  if ((img = RG.loadShape(imgPath)) == null) {
    println("is an invalid image file. Try again...\n");
    selectInput("Please select a SVG file:", "selectImage");
  }
}
////////////////////////////////////////////////////////////////////////
String timestamp() {
  // timestamp
  Date date = new Date();
  SimpleDateFormat sdf = new SimpleDateFormat("yyMMdd-HHmmss");
  return sdf.format(date);
}

//////////////////////////////////////////////////////////////////////
void mouseWheel(MouseEvent event) {
  if (!interactiveViewerEnabled || lineaList == null || lineaList.size() == 0) return;
  if (indiceFine >= lineaList.size()) {
    indiceFine=lineaList.size()-1;
  }
  float e = event.getCount();
  
  if (e < 0) {  // Rotella in avanti
    // Trova la fine del gruppo colore corrente
    color coloreCorrente = brighCol.get(lineaList.get(indiceFine).ic).colore;
    while (indiceFine < lineaList.size() && 
           brighCol.get(lineaList.get(indiceFine).ic).colore == coloreCorrente) {
      indiceFine++;
    }
  } 
  else {  // Rotella all'indietro
    if (indiceFine > 0) {
      // Torna indietro all'inizio del gruppo colore precedente
      color coloreCorrente = brighCol.get(lineaList.get(indiceFine - 1).ic).colore;
      while (indiceFine > 0 && 
             brighCol.get(lineaList.get(indiceFine - 1).ic).colore == coloreCorrente) {
        indiceFine--;
      }
    }
  }
  
  redraw();
}
