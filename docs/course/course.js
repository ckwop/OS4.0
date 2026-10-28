// course.js: the lecture player for docs/course. Shows one .slide at a time
// and reads each slide's .talk aloud with the browser's own speech synthesis,
// a sentence at a time, with captions, a transcript, and "builds": while it
// narrates, parts of the slide marked data-step="n" stay dim until paragraph n
// of the talk begins. In the talk, <span data-say="..."> is spoken as data-say.
// A slide with data-code="n" has a Code button that opens step n of the
// lecture's code tour (<body data-tour="name">, .tours/name.tour) in VS Code,
// through CodeTour's URI handler.
// Keys: space plays or pauses, arrows move, c captions, t transcript, v code.

(() => {
  const slides = [...document.querySelectorAll(".slide")];
  if (!slides.length) return;
  const synth = "speechSynthesis" in window ? window.speechSynthesis : null;

  const store = {
    get(key, fallback) {
      try { const v = localStorage.getItem("os4-course-" + key); return v === null ? fallback : v; }
      catch { return fallback; }
    },
    set(key, value) { try { localStorage.setItem("os4-course-" + key, value); } catch { /* private window */ } },
  };

  // ---- The page furniture

  const progress = document.createElement("div");
  progress.className = "progress";
  progress.innerHTML = "<div></div>";
  const transcript = document.createElement("div");
  transcript.className = "transcript";
  const captions = document.createElement("div");
  captions.className = "captions";
  const controls = document.createElement("div");
  controls.className = "controls";
  controls.innerHTML = `
    <button class="prev" title="Previous slide (left arrow)">&#9664;</button>
    <button class="play primary" title="Play or pause the narration (space)">&#9654; Play</button>
    <button class="next" title="Next slide (right arrow)">&#9654;</button>
    <span class="count"></span>
    <span class="spacer"></span>
    <a class="code" title="Open this slide's step of the code tour in VS Code (v)">Code</a>
    <button class="cc" title="Captions (c)" aria-pressed="false">CC</button>
    <button class="tt" title="Transcript of this slide (t)" aria-pressed="false">Transcript</button>
    <select class="rate" title="Speed">
      <option value="0.8">0.8&times;</option><option value="0.9">0.9&times;</option>
      <option value="1">1&times;</option><option value="1.1">1.1&times;</option>
      <option value="1.25">1.25&times;</option><option value="1.5">1.5&times;</option>
    </select>
    <select class="voice" title="Voice"></select>`;
  document.body.insertBefore(progress, document.querySelector(".stage"));
  document.body.append(transcript, captions, controls);
  const $ = (sel) => controls.querySelector(sel);
  const playButton = $(".play"), rateSelect = $(".rate"), voiceSelect = $(".voice"), codeLink = $(".code");
  const tour = document.body.dataset.tour;

  // ---- Narration: each slide's talk as sentences, with the paragraph each is in

  const sentences = (text) => text.replace(/\s+/g, " ").trim().split(/(?<=[.!?]["'’”)]?)\s+/).filter(Boolean);
  const chunksOf = (slide) => {
    const talk = slide.querySelector(".talk");
    if (!talk) return [];
    return [...talk.querySelectorAll("p")].flatMap((p, para) => {
      const spoken = p.cloneNode(true);
      spoken.querySelectorAll("[data-say]").forEach((e) => e.replaceWith(e.dataset.say));
      return sentences(spoken.textContent).map((text) => ({ para, text }));
    });
  };

  let index = 0;            // the slide shown
  let chunk = 0;            // the next sentence to speak on it
  let playing = false;
  let generation = 0;       // bumped to silence callbacks from speech that was cancelled
  let voice = null;
  let rate = parseFloat(store.get("rate", "1"));
  rateSelect.value = String(rate);

  const setPara = (para) => {
    const slide = slides[index];
    slide.querySelectorAll("[data-step]").forEach((e) => {
      e.classList.toggle("ahead", parseInt(e.dataset.step, 10) > para + 1);
    });
    transcript.querySelectorAll("p").forEach((p, i) => p.classList.toggle("now", i === para));
  };

  const speakFrom = (start) => {
    const mine = ++generation;
    const chunks = chunksOf(slides[index]);
    let k = start;
    const step = () => {
      if (mine !== generation) return;
      if (k >= chunks.length) {
        captions.textContent = "";
        if (index < slides.length - 1) {
          setTimeout(() => { if (mine === generation && playing) show(index + 1); }, 700);
        } else {
          stop();
        }
        return;
      }
      const { para, text } = chunks[k];
      setPara(para);
      captions.textContent = text;
      const u = new SpeechSynthesisUtterance(text);
      if (voice) { u.voice = voice; u.lang = voice.lang; } else { u.lang = "en-GB"; }
      u.rate = rate;
      u.onend = () => { if (mine === generation) { k += 1; chunk = k; step(); } };
      u.onerror = (e) => {
        if (mine !== generation || e.error === "interrupted" || e.error === "canceled") return;
        k += 1; chunk = k; step();
      };
      synth.speak(u);
    };
    step();
  };

  const silence = () => { generation += 1; if (synth) synth.cancel(); captions.textContent = ""; };

  const play = () => {
    if (!synth) return;
    playing = true;
    document.body.classList.add("narrating");
    playButton.innerHTML = "&#10074;&#10074; Pause";
    silence();
    setTimeout(() => speakFrom(chunk), 60);   // some browsers drop a speak() straight after cancel()
  };
  const stop = () => {
    playing = false;
    silence();
    document.body.classList.remove("narrating");
    playButton.innerHTML = "&#9654; Play";
  };

  // ---- Showing a slide

  // Two columns where the code fits. Where it would be cut off: beside a
  // figure, the code moves below at full width; otherwise one column.
  const fit = (slide) => slide.querySelectorAll(".cols").forEach((c) => {
    c.classList.remove("stacked");
    if (![...c.querySelectorAll("pre.code")].some((p) => p.scrollWidth > p.clientWidth + 4)) return;
    const coded = [...c.children].filter((k) => k.matches("pre.code") || k.querySelector("pre.code"));
    if (c.querySelector(":scope > .figure") && coded.length < c.children.length) {
      let at = c;
      coded.forEach((k) => { k.classList.add("below"); at.after(k); at = k; });
      if (c.children.length < 2) c.classList.add("stacked");
    } else {
      c.classList.add("stacked");
    }
  });

  const show = (n) => {
    index = Math.max(0, Math.min(slides.length - 1, n));
    chunk = 0;
    slides.forEach((s, i) => s.classList.toggle("on", i === index));
    fit(slides[index]);
    $(".count").textContent = `${index + 1} / ${slides.length}`;
    progress.firstChild.style.width = `${((index + 1) / slides.length) * 100}%`;
    const talk = slides[index].querySelector(".talk");
    transcript.innerHTML = talk ? talk.innerHTML : "";
    try { history.replaceState(null, "", `#${index + 1}`); } catch { /* file: URLs in some browsers */ }
    setPara(-1);
    const step = slides[index].dataset.code;
    codeLink.hidden = !(tour && step);
    if (tour && step) codeLink.href = `vscode://vsls-contrib.codetour/startTour?tour=${tour}&step=${step}`;
    document.querySelector(".stage").scrollTop = 0;
    if (playing) play(); else silence();
  };

  // ---- Voices: the stored one, else a natural British or other English voice

  const loadVoices = () => {
    if (!synth) return;
    const voices = synth.getVoices().filter((v) => /^en/i.test(v.lang));
    voiceSelect.hidden = !voices.length;
    if (!voices.length) return;
    const wanted = store.get("voice", "");
    const rank = (v) => (v.name === wanted ? 0 : /natural/i.test(v.name) && /GB/i.test(v.lang) ? 1
      : /natural/i.test(v.name) ? 2 : /GB/i.test(v.lang) ? 3 : 4);
    voices.sort((a, b) => rank(a) - rank(b) || a.name.localeCompare(b.name));
    voice = voices[0];
    voiceSelect.innerHTML = "";
    voices.forEach((v) => {
      const o = document.createElement("option");
      o.value = v.name;
      o.textContent = v.name.replace(/^Microsoft /, "").replace(/ - English.*$/, "");
      voiceSelect.append(o);
    });
    voiceSelect.value = voice.name;
  };

  // ---- Wiring

  if (synth) {
    loadVoices();
    synth.onvoiceschanged = loadVoices;
  } else {
    playButton.hidden = rateSelect.hidden = voiceSelect.hidden = true;
    const note = document.createElement("span");
    note.className = "nosound";
    note.textContent = "This browser cannot speak; the transcript is shown instead.";
    controls.insertBefore(note, $(".spacer"));
  }

  const toggle = (button, element, key) => {
    const on = button.getAttribute("aria-pressed") !== "true";
    button.setAttribute("aria-pressed", String(on));
    element.classList.toggle("on", on);
    store.set(key, on ? "1" : "0");
  };
  $(".prev").onclick = () => show(index - 1);
  $(".next").onclick = () => show(index + 1);
  playButton.onclick = () => (playing ? stop() : play());
  codeLink.onclick = () => { if (playing) stop(); };       // reading the code now
  $(".cc").onclick = () => toggle($(".cc"), captions, "captions");
  $(".tt").onclick = () => toggle($(".tt"), transcript, "transcript");
  rateSelect.onchange = () => { rate = parseFloat(rateSelect.value); store.set("rate", rateSelect.value); if (playing) play(); };
  voiceSelect.onchange = () => {
    voice = synth.getVoices().find((v) => v.name === voiceSelect.value) || voice;
    store.set("voice", voiceSelect.value);
    if (playing) play();
  };
  document.addEventListener("keydown", (e) => {
    if (e.target.closest("select") || e.ctrlKey || e.metaKey || e.altKey) return;
    if (e.key === " " || e.key === "k") { e.preventDefault(); playButton.click(); }
    else if (e.key === "ArrowRight" || e.key === "PageDown") { e.preventDefault(); show(index + 1); }
    else if (e.key === "ArrowLeft" || e.key === "PageUp") { e.preventDefault(); show(index - 1); }
    else if (e.key === "c") $(".cc").click();
    else if (e.key === "t") $(".tt").click();
    else if (e.key === "v" && !codeLink.hidden) codeLink.click();
  });
  window.addEventListener("beforeunload", () => synth && synth.cancel());
  window.addEventListener("resize", () => fit(slides[index]));

  if (store.get("captions", "1") === "1") toggle($(".cc"), captions, "captions");
  if (store.get("transcript", synth ? "0" : "1") === "1") toggle($(".tt"), transcript, "transcript");
  show((parseInt(location.hash.slice(1), 10) || 1) - 1);
})();
