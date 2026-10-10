/* Decorative motion follows system preferences and stops in hidden tabs. */
const motionPreference = window.matchMedia?.('(prefers-reduced-motion: reduce)');
let motionPaused = motionPreference?.matches ?? false;
function setMotion(paused) {
  motionPaused = paused;
  document.body.classList.toggle('motion-paused', paused);
  if (paused) document.querySelectorAll('.pointer-spark.is-lit').forEach(spark => spark.classList.remove('is-lit'));
}
setMotion(motionPaused);
motionPreference?.addEventListener?.('change', event => setMotion(event.matches));

// A bounded, decorative atmosphere; reading content remains in front of it.
const atmosphere = document.createElement('div');
atmosphere.className = 'page-atmosphere';
atmosphere.setAttribute('aria-hidden', 'true');
for (let n = 0; n < 3; n++) {
  const ribbon = document.createElement('i');
  ribbon.className = `ambient-ribbon ribbon-${n}`;
  atmosphere.append(ribbon);
}
for (let n = 0; n < 16; n++) {
  const mote = document.createElement('i');
  mote.className = 'ambient-mote';
  const x = n % 2 ? 93 + n % 5 : 2 + n % 5;
  mote.style.cssText = `--x:${x}%;--y:${(n * 23) % 100}%;--delay:-${n * 2.8}s;--time:${18 + n % 7}s;--drift:${n % 2 ? -18 : 18}px`;
  atmosphere.append(mote);
}
document.body.prepend(atmosphere);

const sparkLayer = document.createElement('div');
sparkLayer.className = 'pointer-sparks';
sparkLayer.setAttribute('aria-hidden', 'true');
const sparks = Array.from({ length: 12 }, () => {
  const spark = document.createElement('i');
  spark.className = 'pointer-spark';
  spark.addEventListener('animationend', () => spark.classList.remove('is-lit'));
  sparkLayer.append(spark);
  return spark;
});
document.body.append(sparkLayer);
let sparkIndex = 0;
let lastSpark = 0;
document.addEventListener('pointermove', event => {
  if (motionPaused || motionPreference?.matches || document.hidden || event.pointerType === 'touch') return;
  // Keep spark trails around artwork and outer margins, away from prose.
  const overArt = event.target instanceof Element && event.target.closest('.hero-art, .site-tile img');
  if (!overArt && event.clientX > 48 && event.clientX < window.innerWidth - 48) return;
  if (event.timeStamp - lastSpark < 100) return;
  lastSpark = event.timeStamp;
  const spark = sparks[sparkIndex++ % sparks.length];
  spark.style.left = `${event.clientX}px`;
  spark.style.top = `${event.clientY}px`;
  spark.classList.remove('is-lit');
  void spark.offsetWidth;
  spark.classList.add('is-lit');
}, { passive: true });
function syncVisibility() {
  document.body.classList.toggle('document-resting', document.hidden);
  if (document.hidden) sparks.forEach(spark => spark.classList.remove('is-lit'));
}
document.addEventListener('visibilitychange', syncVisibility);
syncVisibility();

document.querySelectorAll('.hero-art').forEach(art => {
  const motes = document.createElement('div');
  motes.className = 'magic-motes';
  motes.setAttribute('aria-hidden','true');
  const colors = ['#d6ecff','#e6d5ff','#dcf6df'];
  for(let n=0;n<8;n++) {
    const mote = document.createElement('i');
    mote.style.cssText = `--x:${12+n*10}%;--y:${20+(n*17)%62}%;--size:${3+n%3}px;--color:${colors[n%3]};--time:${7+n%4}s;--delay:-${n*1.7}s`;
    motes.append(mote);
  }
  const glow = document.createElement('div');
  glow.className='pointer-glow'; glow.setAttribute('aria-hidden','true');
  art.append(glow,motes);
  art.addEventListener('pointermove',event => {
    if(motionPaused || event.pointerType === 'touch') return;
    const box = art.getBoundingClientRect();
    glow.style.setProperty('--pointer-x',`${event.clientX-box.left}px`);
    glow.style.setProperty('--pointer-y',`${event.clientY-box.top}px`);
  });
});

// The companion is decorative: it greets on mouse hover or a tap, and is never focusable.
document.querySelectorAll('[data-familiar]').forEach(familiar => {
  let resetTimer;
  const greet = () => {
    if (motionPaused) return;
    clearTimeout(resetTimer);
    familiar.classList.remove('is-greeting');
    void familiar.offsetWidth;
    familiar.classList.add('is-greeting');
    resetTimer = setTimeout(() => familiar.classList.remove('is-greeting'), 900);
  };
  familiar.addEventListener('pointerenter', event => { if (event.pointerType === 'mouse') greet(); });
  familiar.addEventListener('click', greet);
});
