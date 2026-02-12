# Plotter Opt

Software scritto in Processing (Java) che utilizza la libreria Geomerative per generare G-code da immagini SVG per un plotter.

## Funzionalità

- Legge un file SVG e trova le forme (parsing tramite Geomerative).
- Effettua l'hatching (riempimento a tratteggio) delle forme mediante linee parallele.
- Crea un file G-code da inviare al plotter per dipingere l'immagine.
- Ottimizza la direzione delle righe di hatching per ridurre gli spostamenti a vuoto.
- Include una vista interattiva per ispezionare forme e righe di hatching a fine elaborazione (tasti 1/2/3/4/9).
- Riduce i duplicati reali nelle linee generate (include anche start/end invertiti).
- Per hatching parallelo evita la chiusura delle linee e scarta segmenti molto corti (<1mm).

## Librerie

- **Geomerative**: Utilizzata per il parsing SVG, creazione RShape e gestione geometria 2D (hatching, segmenti, ecc.).

## Ultimi Aggiornamenti

- **Initial Release**: Upload iniziale del progetto. Include parsing SVG, hatching e generazione GCODE.
- **PEmbroider Hatching**: Aggiunte modalità CONCENTRIC, SPIRAL, PERLIN, VECFIELD (Processing 4).

## Output

Le cartelle di output `GCODE/` sono generate durante l'esecuzione e sono escluse dal repository Git.
