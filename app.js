'use strict';

const statusLine = document.querySelector('#status');
const result = document.querySelector('#result');
const paste = document.querySelector('#paste');
const photo = document.querySelector('#photo');
const grid = document.querySelector('#grid');
const exportActions = document.querySelector('#export');
const copy = document.querySelector('#copy');
const save = document.querySelector('#save');
const copyFeedback = document.querySelector('#copy-feedback');
let outputBlob;
let outputUrl;
const asset = name => new URL(name, document.baseURI).href;

let workerPromise;
let revision = 0;
let scanQueue = Promise.resolve();

function getWorker() {
  workerPromise ??= Tesseract.createWorker('eng', 1, {
    workerPath: asset('worker.min.js'),
    corePath: asset('tesseract-core-lstm.wasm.js'),
    langPath: asset('./'),
    gzip: true,
    workerBlobURL: false,
  }).catch(error => {
    workerPromise = undefined;
    throw error;
  });
  return workerPromise;
}

function rephrase(original) {
  const line = original.replace(/\s+/g, ' ').trim()
    .replace(/\s+(?:to (?:confirm|verify) (?:your account|that you are human)|to continue)[.!:]?$/i, '')
    .replace(/[.!?:]$/, '');
  const tile = '(?:squares?|tiles?|images?|pictures?|photos?)';
  const relation = '(?:contain(?:ing|s)?|show(?:ing|s)?|with|that (?:contain|show)|where you (?:see|can see))';
  const selection = new RegExp('^(?:please )?(?:select|click|tap|choose) all ' + tile + ' ' + relation + ' (.+)$', 'i');
  const question = new RegExp('^which ' + tile + ' ' + relation + ' (.+)$', 'i');
  const capture = line.match(selection) || line.match(question);
  if (!capture) return original;
  const target = capture[1];
  const noun = target.match(/^(?:(a|an) )?([a-z]+(?:[- ][a-z]+){0,3})$/i);
  if (!noun || /\b(?:no|not|without|or|and|except|least|most|only|above|below|next|on|in|under|over|beside|with|the|each|one|two|three|more|than|has|have|is|are)\b/i.test(noun[2])) return original;
  let subject = noun[2];
  if (noun[1]) {
    const words = subject.split(' ');
    const last = words.pop();
    const irregular = { mouse: 'mice', goose: 'geese', ox: 'oxen', wolf: 'wolves',
      calf: 'calves', loaf: 'loaves', person: 'people', man: 'men', woman: 'women',
      child: 'children', deer: 'deer', sheep: 'sheep', fish: 'fish', moose: 'moose',
      aircraft: 'aircraft', bus: 'buses', potato: 'potatoes', tomato: 'tomatoes',
      fox: 'foxes', rhinoceros: 'rhinoceroses' };
    const lower = last.toLowerCase();
    const inflected = Object.prototype.hasOwnProperty.call(irregular, lower) ? irregular[lower]
      : /[^aeiou]y$/i.test(last) ? last.slice(0, -1) + 'ies'
      : /(?:ch|sh|s|x|z)$/i.test(last) ? last + 'es'
      : last + 's';
    words.push(/^[A-Z]/.test(last) ? inflected[0].toUpperCase() + inflected.slice(1) : inflected);
    subject = words.join(' ');
  }
  return 'Select all ' + subject;
}

async function loadImage(file) {
  const url = URL.createObjectURL(file);
  try {
    const image = new Image();
    image.src = url;
    await image.decode();
    const scale = Math.min(1, 1700 / Math.max(image.naturalWidth, image.naturalHeight));
    const canvas = document.createElement('canvas');
    canvas.width = Math.max(1, Math.round(image.naturalWidth * scale));
    canvas.height = Math.max(1, Math.round(image.naturalHeight * scale));
    const context = canvas.getContext('2d', {alpha: false});
    context.fillStyle = '#fff';
    context.fillRect(0, 0, canvas.width, canvas.height);
    context.drawImage(image, 0, 0, canvas.width, canvas.height);
    return canvas;
  } finally {
    URL.revokeObjectURL(url);
  }
}

// Text occupies only a small fraction of an image row. Contiguous rows
// with much more content locate the photos without classifying the motifs.
function gridBounds(canvas) {
  const probe = document.createElement('canvas');
  probe.width = Math.min(240, canvas.width);
  probe.height = Math.max(1, Math.round(canvas.height * probe.width / canvas.width));
  const {width, height} = probe;
  const context = probe.getContext('2d', {willReadFrequently: true});
  context.drawImage(canvas, 0, 0, width, height);
  const pixels = context.getImageData(0, 0, width, height).data;
  const rows = new Uint16Array(height);
  const occupied = new Uint8Array(width * height);
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const index = y * width + x;
      const p = 4 * index;
      const darkest = Math.min(pixels[p], pixels[p + 1], pixels[p + 2]);
      const lightest = Math.max(pixels[p], pixels[p + 1], pixels[p + 2]);
      if (darkest < 215 || lightest - darkest > 25) {
        occupied[index] = 1;
        rows[y]++;
      }
    }
  }

  const bands = [];
  let start = 0;
  for (let y = 0; y <= height; y++) {
    if (y < height && rows[y] >= width * 0.36) continue;
    if (y - start >= Math.max(5, height * 0.035)) {
      const last = bands[bands.length - 1];
      if (last && start - last.end <= height * 0.075) last.end = y;
      else bands.push({start, end: y});
    }
    start = y + 1;
  }
  const band = bands.sort((a, b) => (b.end - b.start) - (a.end - a.start))[0];
  if (!band || band.start < height * 0.035 || band.end - band.start < height * 0.23) return null;

  const columns = new Uint16Array(width);
  for (let y = band.start; y < band.end; y++) {
    for (let x = 0; x < width; x++) columns[x] += occupied[y * width + x];
  }
  const threshold = (band.end - band.start) * 0.18;
  const left = columns.findIndex(count => count >= threshold);
  let right = width;
  while (right > left && columns[right - 1] < threshold) right--;
  if (left < 0 || right - left < width * 0.35) return null;

  const x = Math.floor(Math.max(0, left - 2) * canvas.width / width);
  const y = Math.floor(Math.max(0, band.start - 2) * canvas.height / height);
  return {
    x, y,
    width: Math.ceil(Math.min(width, right + 2) * canvas.width / width) - x,
    height: Math.ceil(Math.min(height, band.end + 2) * canvas.height / height) - y,
  };
}

function wrapTitle(text, context, maxWidth) {
  const lines = [];
  let line = '';
  for (const word of text.trim().split(/\s+/)) {
    const next = line ? line + ' ' + word : word;
    if (line && context.measureText(next).width > maxWidth) {
      lines.push(line);
      line = word;
    } else {
      line = next;
    }
  }
  if (line) lines.push(line);
  return lines;
}

function createOutput(image, bounds, title) {
  const area = bounds ?? {x: 0, y: 0, width: image.width, height: image.height};
  const canvas = document.createElement('canvas');
  const context = canvas.getContext('2d');
  const fontSize = Math.max(12, Math.round(area.width * 0.058));
  const lineHeight = Math.ceil(fontSize * 1.22);
  const padding = Math.ceil(fontSize * 0.62);
  const font = '600 ' + fontSize + 'px system-ui, sans-serif';
  context.font = font;
  const maxWidth = Math.max(1, area.width - padding * 2);
  const lines = title ? wrapTitle(title, context, maxWidth) : [];
  const titleHeight = lines.length ? lines.length * lineHeight + padding * 2 : 0;
  canvas.width = area.width;
  canvas.height = area.height + titleHeight;

  context.fillStyle = '#fff';
  context.fillRect(0, 0, canvas.width, canvas.height);
  context.drawImage(image, area.x, area.y, area.width, area.height,
    0, titleHeight, area.width, area.height);
  context.font = font;
  context.fillStyle = '#161616';
  context.textAlign = 'center';
  context.textBaseline = 'middle';
  lines.forEach((line, index) => {
    context.fillText(line, canvas.width / 2, padding + (index + 0.5) * lineHeight, maxWidth);
  });
  return new Promise(resolve => canvas.toBlob(resolve, 'image/png'));
}

function showOutput(blob, title, bounds) {
  outputBlob = blob;
  outputUrl = URL.createObjectURL(blob);
  grid.alt = [title, bounds ? 'Ausgeschnittenes Bilderraster' : 'Originalbild'].filter(Boolean).join('. ');
  grid.src = outputUrl;
  save.href = outputUrl;
  grid.hidden = false;
  exportActions.hidden = false;
}

copy.addEventListener('click', async () => {
  const blob = outputBlob;
  if (!blob) return;
  try {
    await navigator.clipboard.write([new ClipboardItem({'image/png': blob})]);
    if (blob === outputBlob) copyFeedback.textContent = 'Bild kopiert.';
  } catch {
    if (blob === outputBlob) copyFeedback.textContent =
      'Halte das Bild gedrückt und wähle „Kopieren“ oder tippe auf „PNG speichern“.';
  }
});

async function recognize(canvas, bounds) {
  const worker = await getWorker();
  if (bounds && bounds.y >= 40) {
    const heading = document.createElement('canvas');
    heading.width = canvas.width;
    heading.height = bounds.y;
    heading.getContext('2d').drawImage(canvas, 0, 0);
    const {data} = await worker.recognize(heading);
    if (data.confidence >= 45 && /[a-z]{2}/i.test(data.text)) return data.text.trim();
  }
  // Start above the photos, then expand for taller or lower headings.
  for (const fraction of [0.16, 0.30]) {
    const height = Math.round(canvas.height * fraction);
    if (height < 60) continue;
    const headingCanvas = document.createElement('canvas');
    headingCanvas.width = canvas.width;
    headingCanvas.height = height;
    headingCanvas.getContext('2d').drawImage(canvas, 0, 0);
    const {data} = await worker.recognize(headingCanvas);
    const heading = data.text.trim();
    if (data.confidence >= 82 && (rephrase(heading) !== heading ||
      /^(?:please )?(?:select|choose|tap|click) all [a-z -]+[.!]?$/i.test(heading))) return heading;
  }
  const {data} = await worker.recognize(canvas);
  return /[a-z]{2}/i.test(data.text) && data.confidence >= 30 ? data.text.trim() : '';
}

function submit(file) {
  const current = ++revision;
  result.textContent = '';
  grid.hidden = true;
  exportActions.hidden = true;
  copyFeedback.textContent = '';
  grid.removeAttribute('src');
  save.removeAttribute('href');
  if (outputUrl) URL.revokeObjectURL(outputUrl);
  outputUrl = undefined;
  outputBlob = undefined;
  statusLine.textContent = 'Bild wird gelesen …';
  scanQueue = scanQueue.then(async () => {
    if (current !== revision) return;
    let canvas;
    try {
      canvas = await loadImage(file);
    } catch {
      if (current === revision) statusLine.textContent = 'Das Bild lässt sich nicht öffnen. Versuche es mit einem Screenshot.';
      return;
    }
    try {
      if (current !== revision) return;
      const bounds = gridBounds(canvas);
      const original = await recognize(canvas, bounds);
      if (current !== revision) return;
      const title = original ? rephrase(original) : '';
      const blob = await createOutput(canvas, bounds, title);
      if (current !== revision) return;
      if (!blob) throw new Error('PNG export failed');
      showOutput(blob, title, bounds);
      result.textContent = title;
      statusLine.textContent = original ? '' : 'Kein lesbarer Text gefunden.';
    } catch (error) {
      console.error(error);
      if (current === revision) statusLine.textContent = 'Bild konnte nicht verarbeitet werden. Lade die Seite neu.';
    } finally {
      canvas.width = canvas.height = 1;
    }
  });
}

photo.addEventListener('change', () => {
  if (photo.files[0]) submit(photo.files[0]);
  photo.value = '';
});

function pasteHint(message) {
  if (!result.textContent && !scanPending()) statusLine.textContent = message;
}

function scanPending() {
  return statusLine.textContent === 'Bild wird gelesen …';
}

paste.addEventListener('click', async () => {
  paste.disabled = true;
  try {
    const items = await navigator.clipboard.read();
    for (const item of items) {
      const type = item.types.find(value => value.startsWith('image/'));
      if (type) {
        submit(await item.getType(type));
        return;
      }
    }
    pasteHint('Kein Bild in der Zwischenablage. Nutze „Foto auswählen“.');
  } catch {
    pasteHint('Einsetzen ist hier nicht verfügbar. Nutze „Foto auswählen“.');
  } finally {
    paste.disabled = false;
  }
});

document.addEventListener('paste', event => {
  const image = [...(event.clipboardData?.files ?? [])].find(file => file.type.startsWith('image/'));
  if (image) {
    event.preventDefault();
    submit(image);
  }
});
