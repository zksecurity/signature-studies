function selectButton(buttons, selected) { buttons.forEach(button => button.setAttribute('aria-pressed', String(button === selected))); }
// Selectable native MathML. The hardness input belongs to the reduction;
// the signature adversary receives the public key and oracle replies.
const mi = name => `<mi>${name}</mi>`;
const sub = (name, index) => `<msub>${mi(name)}${typeof index === 'number' ? `<mn>${index}</mn>` : mi(index)}</msub>`;
const sum = (index, expression) => `<munder><mo>∑</mo>${mi(index)}</munder>${expression}`;
const fraction = (numerator, denominator) => `<mfrac><mrow>${numerator}</mrow><mrow>${denominator}</mrow></mfrac>`;
const star = name => `<msup>${mi(name)}<mo>*</mo></msup>`;
const tuple = (...items) => `<mo>(</mo>${items.join('<mo>,</mo>')}<mo>)</mo>`;
const scale = (scalar, point) => `${scalar}<mo>·</mo>${point}`;
const eq = (left, right) => `${left}<mo>=</mo>${right}`;
const math = (label, expression) => `<math aria-label="${label}"><mrow>${expression}</mrow></math>`;
const g1 = sub('g',1), g2 = sub('g',2), x = mi('x'), pk = mi('pk');
const sigma = star('σ'), message = star('m'), topic = star('t'), slot = star('s');
const hash = (...indices) => mi('H') + tuple(...indices);
const pairing = (left, right) => mi('e') + tuple(left,right);
const blsBase = hash(message);
const oopsBase = `<munderover><mo>∑</mo><mrow><mi>j</mi><mo>=</mo><mn>0</mn></mrow><mi>d</mi></munderover><msup>${message}<mi>j</mi></msup><mo>·</mo>${hash(topic,mi('j'))}`;
const proximityBase = `${hash(mi('none'),slot)}<mo>+</mo><munder><mo>∑</mo><mi>k</mi></munder><msub>${message}<mi>k</mi></msub><mo>·</mo>${hash(mi('some')+tuple(mi('k')),slot)}`;
const alpha = mi('α'), m = mi('m'), t = mi('t'), s = mi('s'), j = mi('j');
const display = (label, expression) => `<div class="math-display">${label ? `<span class="math-label">${label}</span>` : ''}${expression}</div>`;
const oopsSum = `<munderover><mo>∑</mo><mrow>${j}<mo>=</mo><mn>0</mn></mrow><mi>d</mi></munderover><msup>${m}${j}</msup><mo>·</mo>${hash(t,j)}`;
const proximitySum = `${hash(mi('none'),s)}<mo>+</mo><munder><mo>∑</mo><mi>k</mi></munder>${sub('m','k')}<mo>·</mo>${hash(mi('some')+tuple(mi('k')),s)}`;
const hardness = {
  dlog: {
    title:'(1,1)-DLog challenge',
    given:math('Given g one, x times g one, g two, x times g two',tuple(g1,scale(x,g1),g2,scale(x,g2))),
    goal:math('the hidden scalar x',x),
    note:'x is sampled uniformly from F and hidden. The reduction receives group elements in both G₁ and G₂ and must recover x. Both AGM extraction branches target this problem.'
  },
  cocdh: {
    title:'Type-3 co-CDH challenge',
    given:math('Given g one, g two, x times g one, x times g two, h',tuple(g1,g2,scale(x,g1),scale(x,g2),mi('h'))),
    goal:math('the group element x times h',scale(x,mi('h'))),
    note:'x is uniform in F; h is uniform in G₁. The reduction receives x·g₁ to simulate signatures. The signature adversary receives pk = x·g₂; no G₂-to-G₁ map is available.'
  }
};
const routes = {
  'bls-agm': {
    verification:blsBase,
    base: math('H of m',hash(m)), signInput: 'message m', sign: math('alpha times H of m',scale(alpha,hash(m))), target: 'a message m* that was never signed',
  },
  'bls-cocdh': {
    verification:blsBase,
    base: math('H of m',hash(m)), signInput: 'message m', sign: math('alpha times H of m',scale(alpha,hash(m))), target: 'a message m* that was never signed',
  },
  oops: {
    verification:oopsBase,
    base: `${math('H of t and j',hash(t,j))}, with ${math('j from 0 to d',`<mn>0</mn><mo>≤</mo>${j}<mo>≤</mo><mi>d</mi>`)}`, signInput: 'scalar m on topic t', sign: math('alpha times the sum over j from 0 to d of m to the j times H of t and j',scale(alpha,`<mrow><mo>(</mo>${oopsSum}<mo>)</mo></mrow>`)), target: 'a fresh scalar/topic pair (m*, t*)',
  },
  proximity: {
    verification:proximityBase,
    base: `${math('H of some k and s',hash(mi('some')+tuple(mi('k')),s))} for each coordinate k, and ${math('H of none and s',hash(mi('none'),s))}`, signInput: 'vector m in slot s', sign: math('alpha times the quantity H of none and s plus the sum over k of m k times H of some k and s',scale(alpha,`<mrow><mo>(</mo>${proximitySum}<mo>)</mo></mrow>`)), target: 'a fresh vector/slot pair (m*, s*)',
  }
};
// Historical walkthrough: preserve links to the earlier 435ddd5 source snapshot.
const sourceBase = 'https://github.com/zksecurity/signature-security-lean/blob/435ddd5021c9e8dc27fe4c1fe8cd1eb87bba5390/Signatures/';
const lean = (label, file, from, to) => ({ label, href: `${sourceBase}${file}#L${from}-L${to}` });
const agmModel = 'Model/LazyAGM.lean', cocdhGame = 'BLS/CoCDH/Spec/LazyGame.lean';
const schemeTerms = {
  'bls-agm': lean('BLS.terms', 'BLS/Spec/LazyAGM.lean', 7, 12),
  oops: lean('OOPS.terms', 'OOPS/Spec/LazyAGM.lean', 10, 18),
  proximity: lean('Proximity.terms', 'Proximity/Spec/LazyAGM.lean', 14, 24)
};
const stepSources = routeKey => routeKey === 'bls-cocdh' ? [
  [lean('key generation in blsEufTightPK', cocdhGame, 141, 146)],
  [lean('hash branch of realOracle', cocdhGame, 103, 108)],
  [lean('signing branch of realOracle', cocdhGame, 109, 116)],
  [lean('TightAdv', cocdhGame, 36, 38)],
  [lean('winning check in blsEufTightPK', cocdhGame, 147, 152), lean('coronReductionProgram', 'BLS/CoCDH/Spec/Coron.lean', 80, 87)]
] : [
  [lean('key generation in experiment', agmModel, 148, 151)],
  [lean('lazyImpl', agmModel, 190, 201)],
  [lean('signing', agmModel, 83, 90), schemeTerms[routeKey]],
  [lean('Output and Adversary', 'Model/SignatureInterface.lean', 28, 41)],
  [lean('winning check in experiment', agmModel, 152, 167),
    ...(routeKey === 'oops' ? [lean('OOPS.admissible', 'OOPS/Spec/LazyAGM.lean', 20, 25)] : routeKey === 'proximity' ? [lean('Proximity.Collision', 'Proximity/Spec/LazyAGM.lean', 28, 36)] : []),
    lean('goodReduction and badReduction', agmModel, 37, 70)]
];
const sourceLinks = links => `<p class="step-source">Earlier source (435ddd5): ${links.map(link => `<a href="${link.href}">${link.label} ↗</a>`).join(' · ')}</p>`;
let gameRoute = 'bls-agm';
let gameStep = 0;
function agmExtraction() {
  const di = sub('d','i');
  const weighted = variable => sum('i', `${di}${sub(variable,'i')}`);
  const answer = expression => `<msup>${x}<mo>′</mo></msup><mo>=</mo>${expression}<mo>=</mo>${x}`;
  const residual = eq(di, `${sub('w','i')}${tuple(message)}<mo>−</mo>${sum('j', `${sub('ξ','j')}${sub('w','i')}${tuple(sub('m','j'))}`)}`);
  // Both branches run in the same order: condition, simulation, equation, requirement.
  return `<section class="extraction-equation" aria-label="AGM extraction equations">
    <h4>Extract the discrete logarithm</h4>
    <p>x′ is the solver’s scalar answer. Let wᵢ(m) be the weight of base Hᵢ in the scheme’s hash expression above; m includes the topic or slot where applicable. For signing replies indexed by j, define:</p>
    ${display('', math('d i equals w i of m star minus the sum over signing replies j of xi j times w i of m j',residual))}
    <p>mⱼ is the signed input and ξⱼ its reply’s output coefficient. β is the generator coefficient; cᵢ sums the output coefficients of explicit hash replies at index i, including repeats.</p>
    <div class="branch good">
      <h5>Good branch ${math('sum i d i rho i is nonzero',`${weighted('ρ')}<mo>≠</mo><mn>0</mn>`)}</h5>
      <p>The solver samples ρᵢ and simulates Hᵢ = ρᵢ·g₁ with pk = x·g₂. A valid forgery yields:</p>
      ${display('', math('x prime equals beta plus sum i c i rho i, divided by sum i d i rho i, equal to x',answer(fraction(`${mi('β')}<mo>+</mo>${sum('i',`${sub('c','i')}${sub('ρ','i')}`)}`,weighted('ρ')))))}
    </div>
    <div class="branch bad">
      <h5>Bad branch · separate solver</h5>
      <p>A separate solver samples aᵢ, bᵢ and κ, then simulates Hᵢ = aᵢ·(x·g₁) + bᵢ·g₁ with pk = κ·g₂. On the zero-denominator event:</p>
      <div class="math-display event">${math('sum i d i times a i x plus b i equals zero',`${sum('i',`${di}<mo>(</mo>${sub('a','i')}${x}<mo>+</mo>${sub('b','i')}<mo>)</mo>`)}<mo>=</mo><mn>0</mn>`)}</div>
      ${display('', math('x prime equals negative sum i d i b i divided by sum i d i a i, equal to x',answer(fraction(`<mo>−</mo>${weighted('b')}`,weighted('a')))))}
      <p>Requires ${math('sum i d i a i is nonzero',`${weighted('a')}<mo>≠</mo><mn>0</mn>`)}. “Bad” names the zero-denominator event; a forgery can still be valid.</p>
    </div>
  </section>`;
}
function gameSteps(routeKey) {
  const route = routes[routeKey];
  const isAGM = routeKey !== 'bls-cocdh';
  return [
    { actor:'challenger', title:'1. Give the adversary its public key', body:'In the signature game, the challenger samples the secret signing scalar α and supplies pk. The separate hardness input above is given to the reduction.', code:display('Public key; α stays private', math('Public key equals alpha times g two',eq(pk,scale(alpha,g2)))) },
    { actor:'oracle', title:'2. Ask for a base', body:'The oracle samples a hash answer on first use and reuses it for the same input.', code:display('Hash query', route.base) },
    { actor:'oracle', title:'3. Request a signature', body:'Signing adapts to earlier replies and uses the shared hash cache. Only explicit replies add visible AGM inputs.', code:display(`Sign ${route.signInput}`, route.sign) },
    // AGM: the forgery comes with the coefficients that step 5's extraction uses (β, cᵢ, ξⱼ).
    isAGM
      ? { actor:'adversary', title:'4. Output a forgery', body:`After choosing its queries, each one possibly based on earlier replies, the adversary outputs a signature σ* on ${route.target}. Because it is algebraic, it also writes σ* as a combination of the group elements it received:`, code:display('Algebraic explanation of σ*', math('sigma star equals beta g one plus the sum over i of c i H i plus the sum over j of xi j sigma j',eq(sigma,`${scale(mi('β'),g1)}<mo>+</mo>${sum('i',`${sub('c','i')}<mo>·</mo>${sub('H','i')}`)}<mo>+</mo>${sum('j',`${sub('ξ','j')}<mo>·</mo>${sub('σ','j')}`)}`))) + '<p>Hᵢ are the hash replies and σⱼ the signing replies. Private random bits are ordinary data, so they get no coefficient.</p>' }
      : { actor:'adversary', title:'4. Output a forgery', body:`After choosing its queries, each one possibly based on earlier replies, the adversary outputs a signature σ* on ${route.target}. In the random-oracle model it gives no account of how σ* was formed.`, code:display('Forgery', math('m star and sigma star',tuple(message,sigma))) },
    { actor:'challenger', title:'5. Check the winning condition', body: routeKey === 'oops' ? 'The scalar/topic pair (m*, t*) must be fresh, with at most d distinct signed messages on t*. Check the pairing equation below.' : routeKey === 'proximity' ? 'The vector/slot pair (m*, s*) must be fresh. Check the pairing equation below. Fresh linear collisions remain in the winning game and contribute a separate, unbounded probability term.' : 'The message m* must never have been signed. Check the pairing equation below using the shared hash cache.', code:display('Signature verification', math('Signature verification: e of sigma star and g two equals e of the target base and public key',eq(pairing(sigma,g2),pairing(route.verification,pk)))), final:true }
  ];
}
// The challenge is a live region, so it is only rewritten when the route changes.
function renderHardness() {
  const target = hardness[gameRoute === 'bls-cocdh' ? 'cocdh' : 'dlog'];
  document.querySelector('#hardness-challenge').innerHTML = `<h3>${target.title}</h3><dl><div><dt>Given to the reduction</dt><dd>${target.given}</dd></div><div><dt>Reduction must output</dt><dd>${target.goal}</dd></div></dl><p>${target.note}</p>`;
}
function renderGame() {
  const steps = gameSteps(gameRoute);
  const step = steps[gameStep];
  let extraction = '';
  if (step.final && gameRoute === 'bls-cocdh') {
    extraction = `<section class="extraction-equation" aria-label="co-CDH extraction equation"><h4>Extract the co-CDH solution</h4><p>When the reduction embeds h at m*, H(m*) = ρ·g₁ + h. On a valid forgery and a non-aborting simulation:</p>${display('', math('Z equals sigma star minus rho times x g one, equal to x times h',`${mi('Z')}<mo>=</mo>${sigma}<mo>−</mo>${scale(mi('ρ'),`<mrow>${tuple(scale(x,g1))}</mrow>`)}<mo>=</mo>${scale(x,mi('h'))}`))}<p>Z is the solver’s output in G₁. It subtracts the known mask ρ·(x·g₁) from the forged signature σ* to recover x·h.</p></section>`;
  } else if (step.final) {
    extraction = agmExtraction();
  }
  document.querySelector('#transcript').innerHTML = `<h3>${step.title}</h3><p>${step.body}</p>${step.code}${sourceLinks(stepSources(gameRoute)[gameStep])}${extraction}`;
  document.querySelectorAll('[data-actor]').forEach(actor => actor.classList.toggle('active', actor.dataset.actor === step.actor));
  document.querySelector('#step-count').textContent = `Step ${gameStep + 1} of ${steps.length}`;
  document.querySelector('#step-status').textContent = `Step ${gameStep + 1} of ${steps.length}: ${step.title.replace(/^\d+\.\s*/, '')}`;
  document.querySelector('#previous-step').disabled = gameStep === 0;
  document.querySelector('#next-step').textContent = gameStep === steps.length - 1 ? 'Start again' : 'Next step';
}
document.querySelectorAll('[data-game]').forEach(button => button.addEventListener('click', () => {
  gameRoute = button.dataset.game;
  gameStep = 0;
  selectButton(document.querySelectorAll('[data-game]'), button);
  renderHardness();
  renderGame();
}));
document.querySelector('#previous-step')?.addEventListener('click', () => { gameStep = Math.max(0, gameStep - 1); renderGame(); });
document.querySelector('#next-step')?.addEventListener('click', () => { gameStep = (gameStep + 1) % 5; renderGame(); });


if (document.querySelector('#transcript')) { renderHardness(); renderGame(); }
