boolean interactiveViewerEnabled = false;
int interactiveVisibleSteps = 0;
boolean interactiveDotsEnabled = false;

ArrayList<InteractiveGroup> interactiveGroups = new ArrayList<InteractiveGroup>();
ArrayList<InteractiveStep> interactiveSteps = new ArrayList<InteractiveStep>();
IntList interactiveGroupStart = new IntList();
IntList interactiveGroupEnd = new IntList();
ArrayList<InteractiveDot> interactiveDots = new ArrayList<InteractiveDot>();

class InteractiveDot {
  RPoint p;
  int dotColor;
  float d;

  InteractiveDot(RPoint p, int dotColor, float d) {
    this.p = p;
    this.dotColor = dotColor;
    this.d = d;
  }
}

class InteractiveLine {
  RPoint start;
  RPoint end;

  InteractiveLine(RPoint start, RPoint end) {
    this.start = start;
    this.end = end;
  }
}

class InteractiveGroup {
  int paletteIndex;
  int colorRank;
  int originalIndex;
  ArrayList<RPoint[]> contours = new ArrayList<RPoint[]>();
  ArrayList<InteractiveLine> hatchLines = new ArrayList<InteractiveLine>();

  InteractiveGroup(int paletteIndex, int colorRank, int originalIndex) {
    this.paletteIndex = paletteIndex;
    this.colorRank = colorRank;
    this.originalIndex = originalIndex;
  }
}

class InteractiveStep {
  int kind;
  int groupIndex;
  int hatchIndex;

  InteractiveStep(int kind, int groupIndex, int hatchIndex) {
    this.kind = kind;
    this.groupIndex = groupIndex;
    this.hatchIndex = hatchIndex;
  }
}

void interactiveViewerInit() {
  interactiveGroups.clear();
  interactiveSteps.clear();
  interactiveGroupStart.clear();
  interactiveGroupEnd.clear();
  interactiveDots.clear();

  ArrayList<InteractiveLine> pendingHatches = new ArrayList<InteractiveLine>();
  int groupCounter = 0;

  for (int i = 0; i < paperFormList.size(); i++) {
    Forma f = paperFormList.get(i);
    if (f.type == 1) {
      InteractiveLine l = interactiveLineFromShape(f.sh);
      if (l != null) pendingHatches.add(l);
      continue;
    }

    if (f.type == 0) {
      int colorRank = interactiveColorRankForPaletteIndex(f.ic);
      InteractiveGroup g = new InteractiveGroup(f.ic, colorRank, groupCounter++);
      g.hatchLines.addAll(pendingHatches);
      pendingHatches.clear();

      ArrayList<RPoint[]> contourPts = interactiveContoursFromShape(f.sh);
      g.contours.addAll(contourPts);

      interactiveGroups.add(g);
    }
  }

  Collections.sort(interactiveGroups, new Comparator<InteractiveGroup>() {
    public int compare(InteractiveGroup a, InteractiveGroup b) {
      int byColor = Integer.compare(a.colorRank, b.colorRank);
      if (byColor != 0) return byColor;
      return Integer.compare(a.originalIndex, b.originalIndex);
    }
  });

  interactiveApplyTravelOptimizationToHatches();

  for (int gi = 0; gi < interactiveGroups.size(); gi++) {
    int start = interactiveSteps.size();
    interactiveGroupStart.append(start);

    interactiveSteps.add(new InteractiveStep(0, gi, -1));
    InteractiveGroup g = interactiveGroups.get(gi);
    for (int hi = 0; hi < g.hatchLines.size(); hi++) {
      interactiveSteps.add(new InteractiveStep(1, gi, hi));
    }

    interactiveGroupEnd.append(interactiveSteps.size());
  }

  interactiveVisibleSteps = interactiveSteps.size();
  interactiveViewerEnabled = true;
  interactiveDotsEnabled = false;
  noLoop();
  redraw();
}

void keyPressed() {
  if (!interactiveViewerEnabled) return;

  if (key == '9') {
    interactiveVisibleSteps = interactiveSteps.size();
    interactiveDotsEnabled = false;
    interactiveDots.clear();
    redraw();
    return;
  }

  if (!interactiveDotsEnabled && (key == '1' || key == '2' || key == '3' || key == '4')) {
    interactiveVisibleSteps = 0;
    interactiveDotsEnabled = true;
    interactiveDots.clear();
  }

  int prevVisibleSteps = interactiveVisibleSteps;

  if (key == '1') {
    if (interactiveVisibleSteps < interactiveSteps.size()) interactiveVisibleSteps++;
    interactiveAddDotsForNewSteps(prevVisibleSteps, interactiveVisibleSteps);
    redraw();
    return;
  }

  if (key == '2') {
    if (interactiveVisibleSteps > 0) interactiveVisibleSteps--;
    redraw();
    return;
  }

  if (key == '3') {
    interactiveAdvanceWholeGroup();
    interactiveAddDotsForNewSteps(prevVisibleSteps, interactiveVisibleSteps);
    redraw();
    return;
  }

  if (key == '4') {
    interactiveBackWholeGroup();
    redraw();
    return;
  }
}

void interactiveAddDotsForNewSteps(int fromStepExclusive, int toStepInclusive) {
  if (!interactiveDotsEnabled) return;
  if (toStepInclusive <= fromStepExclusive) return;

  int start = max(0, fromStepExclusive);
  int end = min(interactiveSteps.size(), toStepInclusive);
  for (int si = start; si < end; si++) {
    InteractiveStep st = interactiveSteps.get(si);
    if (st.kind != 1) continue;

    InteractiveGroup g = interactiveGroups.get(st.groupIndex);
    InteractiveLine l = g.hatchLines.get(st.hatchIndex);
    if (l == null || l.start == null || l.end == null) continue;

    interactiveDots.add(new InteractiveDot(new RPoint(l.start), #FF0000, 6));
    interactiveDots.add(new InteractiveDot(new RPoint(l.end), #00FF00, 6));
  }
}

void interactiveAdvanceWholeGroup() {
  if (interactiveVisibleSteps >= interactiveSteps.size()) return;

  int g = interactiveGroupIndexForStepPosition(interactiveVisibleSteps);
  int end = interactiveGroupEnd.get(g);
  if (interactiveVisibleSteps < end) {
    interactiveVisibleSteps = end;
  }
}

void interactiveBackWholeGroup() {
  if (interactiveVisibleSteps <= 0) return;

  int lastVisibleStep = interactiveVisibleSteps - 1;
  int g = interactiveGroupIndexForStepPosition(lastVisibleStep);
  interactiveVisibleSteps = interactiveGroupStart.get(g);
}

int interactiveGroupIndexForStepPosition(int stepPos) {
  for (int g = 0; g < interactiveGroupEnd.size(); g++) {
    if (stepPos < interactiveGroupEnd.get(g)) return g;
  }
  return max(0, interactiveGroupEnd.size() - 1);
}

void interactiveViewerDraw() {
  interactiveViewerDrawAt(0);
}

void interactiveViewerDrawAt(float baseX) {
  pushMatrix();
  translate(baseX, 0);
  int currentStepIndex = interactiveVisibleSteps - 1;
  boolean highlightCurrent = interactiveDotsEnabled;

  for (int si = 0; si < interactiveVisibleSteps; si++) {
    InteractiveStep st = interactiveSteps.get(si);
    InteractiveGroup g = interactiveGroups.get(st.groupIndex);
    color c = interactiveColorForGroup(g);
    boolean isCurrent = (si == currentStepIndex);

    if (st.kind == 0) {
      stroke(c);
      strokeWeight((highlightCurrent && isCurrent) ? 2 : 1);
      noFill();
      interactiveDrawContours(g.contours);
      continue;
    }

    InteractiveLine l = g.hatchLines.get(st.hatchIndex);
    stroke(c);
    strokeWeight((highlightCurrent && isCurrent) ? (sovr + 2) : sovr);
    noFill();
    interactiveDrawLine(l.start, l.end);
  }

  if (interactiveDotsEnabled) {
    noStroke();
    for (int i = 0; i < interactiveDots.size(); i++) {
      InteractiveDot d = interactiveDots.get(i);
      fill(d.dotColor);
      interactiveDrawDot(d.p, d.d);
    }
  }
  popMatrix();
}

int interactiveColorRankForPaletteIndex(int paletteIndex) {
  for (int i = 0; i < brighCol.size(); i++) {
    if (brighCol.get(i).indice == paletteIndex) return i;
  }
  return paletteIndex;
}

color interactiveColorForGroup(InteractiveGroup g) {
  if (g.colorRank >= 0 && g.colorRank < brighCol.size()) return brighCol.get(g.colorRank).colore;
  if (g.paletteIndex >= 0 && g.paletteIndex < palette.length) return palette[g.paletteIndex];
  return #000000;
}

void interactiveApplyTravelOptimizationToHatches() {
  PVector simPos = new PVector(0, 0);
  int simColorRank = -1;

  for (int gi = 0; gi < interactiveGroups.size(); gi++) {
    InteractiveGroup g = interactiveGroups.get(gi);
    if (g.colorRank != simColorRank) {
      simColorRank = g.colorRank;
      if (simColorRank >= 0) {
        setCoordColor(simColorRank);
        simPos.x = xCol;
        simPos.y = yCol;
      }
    }

    for (int hi = 0; hi < g.hatchLines.size(); hi++) {
      InteractiveLine l = g.hatchLines.get(hi);
      if (l == null) continue;

      float ds = (simPos.x - l.start.x) * (simPos.x - l.start.x) + (simPos.y - l.start.y) * (simPos.y - l.start.y);
      float de = (simPos.x - l.end.x) * (simPos.x - l.end.x) + (simPos.y - l.end.y) * (simPos.y - l.end.y);

      if (de < ds) {
        RPoint tmp = l.start;
        l.start = l.end;
        l.end = tmp;
      }

      simPos.x = l.end.x;
      simPos.y = l.end.y;
    }
  }
}

void interactiveDrawContours(ArrayList<RPoint[]> contours) {
  for (int ci = 0; ci < contours.size(); ci++) {
    RPoint[] pts = contours.get(ci);
    if (pts == null || pts.length < 2) continue;

    for (int i = 0; i < pts.length - 1; i++) {
      interactiveDrawLine(pts[i], pts[i + 1]);
    }
    interactiveDrawLine(pts[pts.length - 1], pts[0]);
  }
}

void interactiveDrawLine(RPoint a, RPoint b) {
  float ax = (a.x - xOffset) / factor;
  float ay = (a.y - yOffset) / factor;
  float bx = (b.x - xOffset) / factor;
  float by = (b.y - yOffset) / factor;
  line(ax, ay, bx, by);
}

void interactiveDrawDot(RPoint p, float d) {
  float x = (p.x - xOffset) / factor;
  float y = (p.y - yOffset) / factor;
  ellipse(x, y, d, d);
}

ArrayList<RPoint[]> interactiveContoursFromShape(RShape sh) {
  ArrayList<RPoint[]> res = new ArrayList<RPoint[]>();
  if (sh == null) return res;

  RPolygon poly = sh.toPolygon();
  if (poly == null || poly.contours == null) return res;

  for (int k = 0; k < poly.contours.length; k++) {
    if (poly.contours[k] == null || poly.contours[k].points == null) continue;
    res.add(poly.contours[k].points);
  }

  return res;
}

InteractiveLine interactiveLineFromShape(RShape sh) {
  if (sh == null) return null;
  RPolygon poly = sh.toPolygon();
  if (poly == null || poly.contours == null || poly.contours.length == 0) return null;
  if (poly.contours[0] == null || poly.contours[0].points == null) return null;

  RPoint[] pts = poly.contours[0].points;
  if (pts.length == 0) return null;
  if (pts.length == 1) return new InteractiveLine(pts[0], pts[0]);

  int endIndex = pts.length - 1;
  while (endIndex > 0 && pts[endIndex].x == pts[0].x && pts[endIndex].y == pts[0].y) {
    endIndex--;
  }
  RPoint start = pts[0];
  RPoint end = pts[endIndex];
  if (endIndex == 0 && pts.length > 1) end = pts[1];

  return new InteractiveLine(start, end);
}
