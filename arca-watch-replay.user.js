// ==UserScript==
// @name         아카라이브 같이 보기 다시 보기
// @namespace    local.arca.watch-replay
// @version      0.5.7
// @description  종료된 방의 YouTube 영상과 댓글을 같이 보기 화면으로 재생합니다.
// @match        https://arca.live/b/*/*
// @match        https://arca.live/r/*/*
// @grant        none
// @run-at       document-idle
// @updateURL    https://raw.githubusercontent.com/Ling-Bleune/arca-watch-replay/main/arca-watch-replay.user.js
// @downloadURL  https://raw.githubusercontent.com/Ling-Bleune/arca-watch-replay/main/arca-watch-replay.user.js
// @supportURL   https://github.com/Ling-Bleune/arca-watch-replay/issues
// ==/UserScript==

(() => {
  'use strict';
  const path = location.pathname.match(/^\/(?:b|r)\/([^/]+)\/(\d+)\/?$/);
  if (!path || document.getElementById('arca-watch-replay')) return;
  const articlePath = `/b/${path[1]}/${path[2]}`;
  const articleURL = new URL(articlePath, location.origin);
  const CACHE_PREFIX = 'arca-watch-replay-v2:', CACHE_TTL = 24*60*60*1000;
  const storageKey = `${CACHE_PREFIX}${articlePath}`;
  let cacheTouchedAt = Date.now();
  const comments = new Map();
  let ordered = [], start = NaN, offset = 0, elapsed = 0, rate = 1;
  let playing = false, anchor = performance.now(), player = null, ready = false;
  let mode = 'youtube', opened = false, apiPromise = null, collection = null;
  let pendingSeek = null, generation = 0, lastRange = '', objectURL = null;
  let previousOverflow = '';
  let endAt = NaN, manualEnd = false, durationHint = 0;
  let modifiedAt = NaN, endPreference = 'modified', userScrollUntil = 0;
  let articleMetadataChecked = false;
  let seekPending = false;
  const pageCache = new Map();
  const REQUEST_GAP = 1500, AHEAD = 90000, BEHIND = 60000;
  let maxPage = 1, lastRequestAt = -Infinity, bufferJob = null, retryAt = 0, bottomFrame = 0;

  function parseDate(value) {
    if (typeof value !== 'string') return NaN;
    const m = value.trim().match(/^(\d{4})[-./](\d{1,2})[-./](\d{1,2})[T\s]+(\d{1,2}):(\d{2})(?::(\d{2}))?(?:\.(\d+))?(Z|[+-]\d{2}:?\d{2})?$/i);
    if (!m) return NaN;
    const [, y, mo, d, h, mi, sec = '0', fraction = '', zone] = m;
    return Date.parse(`${y}-${mo.padStart(2,'0')}-${d.padStart(2,'0')}T${h.padStart(2,'0')}:${mi}:${sec.padStart(2,'0')}${fraction ? '.'+fraction : ''}${zone || '+09:00'}`);
  }
  function kstInput(ms) { return new Date(ms + 9*3600000).toISOString().slice(0,19); }
  function format(seconds) {
    const s = Math.max(0,Math.floor(seconds));
    return `${s >= 3600 ? Math.floor(s/3600)+':' : ''}${String(Math.floor(s/60)%60).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;
  }
  function youtubeID(value) {
    if (typeof value !== 'string') return null;
    const text = value.trim();
    if (/^[\w-]{11}$/.test(text)) return text;
    try {
      const url = new URL(text);
      let id = null;
      if (url.hostname === 'youtu.be') id = url.pathname.split('/')[1];
      else if (/^(?:www\.|m\.)?youtube(?:-nocookie)?\.com$/.test(url.hostname)) {
        id = url.searchParams.get('v') || url.pathname.match(/^\/(?:live|embed|shorts)\/([\w-]+)/)?.[1];
      }
      return id && /^[\w-]{11}$/.test(id) ? id : null;
    } catch { return null; }
  }
  function relayConfig(doc) {
    if (doc === document && window.LiveConfig?.relay) return window.LiveConfig.relay;
    for (const script of doc.querySelectorAll('script:not([src])')) {
      const match = script.textContent.match(/window\.LiveConfig\s*=\s*(\{.*\})\s*;?\s*$/s);
      if (!match) continue;
      try { return JSON.parse(match[1]).relay || null; } catch { /* HTML의 코드는 실행하지 않습니다. */ }
    }
    return null;
  }
  function detectVideo(doc) {
    const relay = relayConfig(doc);
    const candidates = [relay?.url, doc.querySelector('.relay-card .og-href')?.textContent];
    for (const el of doc.querySelectorAll('.relay-frame-area iframe, .article-content iframe, .relay-card a, .article-content a')) {
      candidates.push(el.getAttribute('src'), el.getAttribute('href'));
    }
    return candidates.map(youtubeID).find(Boolean) || '';
  }
  function modifiedDate(doc) {
    if (![...doc.querySelectorAll('.relay-card')].some(el => el.textContent.includes('종료된 방'))) return NaN;
    const row = [...doc.querySelectorAll('.article-info .date')].find(el => el.querySelector('.head')?.textContent.trim() === '수정일');
    const time = row?.querySelector('time');
    return parseDate(time?.getAttribute('datetime') || time?.textContent);
  }
  function safeMedia(value, base) {
    if (typeof value !== 'string' || !value.trim()) return null;
    // Chrome 저장 HTML의 상대 경로는 원격 CDN 주소로 복원할 수 없습니다.
    if (!/^(?:https:\/\/|\/\/|\/)/i.test(value)) return null;
    try {
      const url = new URL(value.startsWith('//') ? `https:${value}` : value, base);
      return url.protocol === 'https:' && /(^|\.)arca\.live$/.test(url.hostname) ? url.href : null;
    } catch { return null; }
  }
  function parseComments(doc, base) {
    const result = [], rows = [...doc.querySelectorAll('#comment .comment-item, .article-comment .comment-item')];
    let invalid = 0, missingMedia = 0;
    for (const row of rows) {
      if (row.classList.contains('deleted')) continue;
      const body = row.querySelector(':scope > .content > .message');
      const info = row.querySelector(':scope > .content > .info-row');
      const time = info?.querySelector('time');
      const at = [time?.getAttribute('datetime'),time?.getAttribute('data-datetime'),time?.textContent].map(parseDate).find(Number.isFinite);
      if (!body || !Number.isFinite(at)) { invalid++; continue; }
      const user = info.querySelector('.user-info a[data-filter], .user-info a');
      const author = user?.textContent.trim() || '익명';
      const identity = user?.getAttribute('data-filter') || author;
      const textNode = body.querySelector('.text');
      const copy = (textNode || body).cloneNode(true);
      copy.querySelectorAll('script,style,button,.PlayBackRatePanelYPSC,.emoticon-wrapper,.modified,.btn-more,video,img').forEach(el => el.remove());
      const text = copy.textContent.trim();
      const media = [];
      for (const el of body.querySelectorAll('img.emoticon, video.emoticon, .emoticon-wrapper img, .emoticon-wrapper video')) {
        const src = safeMedia(el.getAttribute('src'),base);
        if (!src) { missingMedia++; continue; }
        media.push({type:el.tagName === 'VIDEO' ? 'video' : 'image',src,poster:safeMedia(el.getAttribute('poster'),base)});
      }
      const id = row.id.replace(/^c_/,'');
      if (!id) { invalid++; continue; }
      result.push({id,at,author,identity,text,media,missingMedia:!text && !media.length});
    }
    return {comments:result,invalid,missingMedia,rows:rows.length};
  }
  function commentPages(doc) {
    const pages = new Set();
    for (const link of doc.querySelectorAll('a[href]')) {
      try {
        const url = new URL(link.getAttribute('href'),articleURL);
        if (url.origin !== articleURL.origin || url.pathname !== articlePath) continue;
        const cp = url.searchParams.get('cp');
        if (!cp || !/^\d+$/.test(cp) || Number(cp) < 1 || Number(cp) > 10000) continue;
        // 신고/답글 링크의 쿼리에서도 페이지 번호만 읽고, 요청은 정규화합니다.
        pages.add(Number(cp));
      } catch { /* invalid href */ }
    }
    return [...pages].sort((a,b) => a-b);
  }
  function upperBound(at) {
    let lo = 0, hi = ordered.length;
    while (lo < hi) { const mid = (lo+hi) >>> 1; if (ordered[mid].at <= at) lo = mid+1; else hi = mid; }
    return lo;
  }

  const host = document.createElement('div'); host.id = 'arca-watch-replay'; document.body.append(host);
  const root = host.attachShadow({mode:'open'});
  root.innerHTML = `
    <style>
      :host{font:14px/1.5 system-ui,sans-serif;color:#e9edf4;--bg:#151922;--line:#343d4d}
      *{box-sizing:border-box}button,input,select{font:inherit}button{cursor:pointer}button:disabled{opacity:.5;cursor:default}
      button,input,select{border:1px solid #49556a;border-radius:6px;padding:6px 9px;background:#252d3b;color:inherit}
      button:hover{background:#38445a}input{min-width:0}label{font-size:12px;color:#b7c3d6}a{color:#9bd0ff}
      #launch{position:fixed;bottom:20px;left:20px;z-index:2147483645;display:flex;align-items:center;justify-content:center;width:46px;height:46px;border-radius:50%;padding:0;background:#1e1e1e;box-shadow:0 4px 20px #0006}
      #launch:hover{background:#737373}
      #launch svg{width:22px;height:22px;fill:currentColor}#launch:focus-visible{outline:2px solid #b7d7ff;outline-offset:3px}
      #overlay{position:fixed;inset:0;z-index:2147483646;background:var(--bg);display:flex;flex-direction:column}
      [hidden]{display:none!important}
      .layout{flex:1;min-height:0;display:grid;grid-template-columns:minmax(0,1fr) 24rem}
      .left{min-width:0;min-height:0;display:flex;flex-direction:column;background:#080a0e}
      #video-box{flex:1;min-height:220px;display:flex;align-items:center;justify-content:center;position:relative}
      #video-box iframe{width:100%;height:100%;border:0;position:absolute;inset:0}
      #placeholder{padding:32px;color:#abb6c8;text-align:center}.transport{padding:12px 16px;border-top:1px solid var(--line);background:#1d2330;display:grid;gap:8px}
      .row{display:flex;align-items:center;gap:8px;flex-wrap:wrap}.grow{flex:1}
      #clock{font-variant-numeric:tabular-nums}#seconds{width:88px}#rate{width:76px}#status{font-size:12px;color:#b7c7e1;min-height:18px;overflow-wrap:anywhere}
      .right{border-left:1px solid var(--line);display:flex;flex-direction:column;min-height:0;background:#191f2b}
      .chat-head{padding:12px 16px;border-bottom:1px solid var(--line);display:flex;align-items:center;justify-content:space-between}
      #chat{flex:1;overflow:auto;min-height:0;padding:8px 16px;overflow-anchor:none;scroll-behavior:auto}
      .message{padding:6px 0;overflow-wrap:anywhere}.stamp{font-size:10px;color:#8190a7;margin-right:7px}.author{font-weight:700;margin-right:7px}.body{white-space:pre-wrap}
      .arcacons{display:inline-flex;gap:0;flex-wrap:nowrap;vertical-align:top;line-height:0}.arcacon{display:block;flex:none;width:50px;height:50px;object-fit:contain;margin:0;padding:0;border:0}.missing{color:#8894a9;font-size:12px;line-height:1.5}
      .chat-foot{padding:10px 16px;border-top:1px solid var(--line);color:#9aabc4;font-size:12px}
      #buffer-state{flex:none;height:40px;display:flex;align-items:center;min-width:0;padding:0 16px;border-top:1px solid var(--line);background:#202a3b;color:#c8dcff;font-size:12px}
      #buffer-label{min-width:0;overflow:hidden;white-space:nowrap;text-overflow:ellipsis}
      .modal{position:absolute;inset:0;z-index:5;background:#0009;display:flex;align-items:center;justify-content:center;padding:16px}
      .modal-card{width:760px;max-width:100%;max-height:90dvh;overflow:auto;background:#222b39;border:1px solid var(--line);border-radius:10px;box-shadow:0 10px 50px #0008}
      .modal-head{padding:12px 16px;border-bottom:1px solid var(--line)}
      .settings{padding:16px;display:grid;grid-template-columns:1fr 1fr;gap:8px 16px}.settings label input{display:block;width:100%;margin-top:3px}
      .settings .wide{grid-column:1/-1}.hint{font-size:12px;color:#9eaec6;margin:0}#offset{max-width:120px}
      @media(max-width:991px){.layout{display:flex;flex-direction:column}.left{flex:none;height:48%;min-height:160px}.right{flex:1;min-height:100px;border-left:0;border-top:1px solid var(--line)}#video-box{min-height:130px}}
      @media(max-width:620px){.transport{padding:7px 10px}.settings{grid-template-columns:1fr}.settings .wide{grid-column:auto}}
    </style>
    <button id="launch" aria-label="같이 보기 다시 보기" title="같이 보기 다시 보기"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="M8 5v14l11-7z"/></svg></button>
    <section id="overlay" hidden>
      <div id="settings" class="modal" role="dialog" aria-modal="true" aria-labelledby="settings-title" hidden>
        <div class="modal-card">
        <div class="row modal-head"><b id="settings-title" class="grow">영상·끝 시각 설정 / 댓글 저장</b><button id="dismiss-settings">닫기</button></div>
        <div class="settings">
          <label>YouTube 영상 주소<input id="url" placeholder="https://youtu.be/…"></label>
          <label>영상이 실제로 끝난 시각 (한국 시각)<input id="end" type="datetime-local" step="1"></label>
          <label>영상 전체 길이 (초 · YouTube 자동)<input id="duration" type="number" min="1" step="0.001" placeholder="YouTube에서 자동 확인" readonly></label>
          <div class="row"><button id="load-video">영상 적용</button><select id="mode" aria-label="재생 기준"><option value="youtube">YouTube에 동기화</option><option value="timer">별도 타이머</option></select></div>
          <div class="row wide"><label>채팅 보정(초) <input id="offset" type="number" value="0" step="1"></label><button id="modified">게시글 수정일에 영상 끝 맞추기</button><button id="last">마지막 댓글에 영상 끝 맞추기</button></div>
          <p id="basis" class="hint wide"></p>
          <p class="hint wide">끝 시각에서 영상 전체 길이를 빼서 싱크를 계산합니다. 기본값은 종료된 게시글의 수정일입니다. 종료 후 본문을 다시 수정했다면 끝 시각을 직접 보정하세요. 수정일이 없으면 마지막 댓글을 임시 기준으로 사용합니다. 보정 +값은 채팅을 일찍 표시합니다.</p>
          <div class="row wide"><button id="export">JSON 내보내기</button><button id="import">JSON / 저장 HTML 가져오기</button><button id="collect">전체 댓글 보관</button><button id="retry">주변 댓글 다시 확인</button><button id="clear">수집 초기화</button><a id="article-link" target="_blank" rel="noopener">일반 게시글 열기</a><button id="close">게시글로 돌아가기</button></div>
          <input id="file" type="file" accept=".json,.html,.htm" multiple hidden>
          <div class="transport wide" id="timer-controls" hidden>
            <div class="row"><button id="play">재생</button><button id="reset">처음</button><select id="rate" aria-label="배속"><option value="0.5">0.5×</option><option value="1" selected>1×</option><option value="1.5">1.5×</option><option value="2">2×</option></select><span id="clock">00:00</span><span class="grow"></span><input id="seconds" type="number" min="0" step="1" value="0" aria-label="이동할 초"><button id="jump">초로 이동</button></div>
          </div>
          <div id="status" class="wide" role="status">영상 끝 시각을 기준으로 동기화합니다.</div>
        </div>
        </div>
      </div>
      <div class="layout">
        <div class="left">
          <div id="video-box"><div id="placeholder">영상 준비 중…</div></div>
        </div>
        <aside class="right">
          <div class="chat-head"><b>다시 보기 채팅 <small id="count">0개</small></b><button id="show-settings" aria-haspopup="dialog">설정</button></div>
          <div id="chat" tabindex="0" aria-label="다시 보기 채팅"><div id="messages"></div></div>
          <div class="chat-foot"><label><input id="follow" type="checkbox" checked> 자동 스크롤</label> · 읽기 전용 <span id="shown"></span></div>
          <div id="buffer-state" role="status" aria-live="polite" hidden><span id="buffer-label"></span></div>
        </aside>
      </div>
    </section>`;
  const $ = id => root.getElementById(id);
  const status = text => { $('status').textContent = text; };
  function setBuffer(text, busy = true) {
    if ($('buffer-label').textContent !== text) $('buffer-label').textContent = text;
    $('buffer-label').title = text;
    $('buffer-state').hidden = !text;
    $('chat').setAttribute('aria-busy',String(!!text && busy));
  }
  $('article-link').href = articleURL.href;
  function scheduleBottom() {
    if (bottomFrame) return;
    bottomFrame = requestAnimationFrame(() => {
      bottomFrame = 0;
      if (opened && $('follow').checked) $('chat').scrollTop = $('chat').scrollHeight;
    });
  }
  const chatResize = new ResizeObserver(scheduleBottom);
  chatResize.observe($('messages')); chatResize.observe($('chat'));
  $('chat').addEventListener('wheel',e => {
    userScrollUntil = performance.now()+500;
    if (e.deltaY<0) $('follow').checked = false;
    else if (e.deltaY>0 && $('chat').scrollHeight-$('chat').clientHeight-$('chat').scrollTop<=2) { $('follow').checked = true; scheduleBottom(); }
  },{passive:true});
  for (const event of ['touchstart','touchmove']) $('chat').addEventListener(event,() => { userScrollUntil = performance.now()+500; },{passive:true});
  $('chat').addEventListener('pointerdown',() => { userScrollUntil = Infinity; });
  document.addEventListener('pointerup',() => { if (userScrollUntil === Infinity) userScrollUntil = performance.now()+500; });
  document.addEventListener('pointercancel',() => { if (userScrollUntil === Infinity) userScrollUntil = performance.now()+500; });
  $('chat').addEventListener('keydown',e => {
    if (!['ArrowUp','ArrowDown','PageUp','PageDown','Home','End',' '].includes(e.key)) return;
    userScrollUntil = performance.now()+500;
    if (['ArrowUp','PageUp','Home'].includes(e.key) || e.key===' ' && e.shiftKey) $('follow').checked = false;
  });
  $('chat').addEventListener('scroll',() => {
    if (performance.now()>userScrollUntil) return;
    const chat = $('chat');
    $('follow').checked = chat.scrollHeight-chat.clientHeight-chat.scrollTop<=2;
    if ($('follow').checked) scheduleBottom();
  },{passive:true});
  function showSettings() { $('settings').hidden = false; $('dismiss-settings').focus(); }
  function hideSettings() { $('settings').hidden = true; if (opened) $('show-settings').focus(); }
  $('show-settings').onclick = showSettings; $('dismiss-settings').onclick = hideSettings;
  $('settings').onclick = e => { if (e.target === $('settings')) hideSettings(); };

  function cleanupCaches(now = Date.now()) {
    const keys = [];
    try {
      for (let i=0;i<localStorage.length;i++) { const key = localStorage.key(i); if (key?.startsWith(CACHE_PREFIX)) keys.push(key); }
      for (const key of keys) {
        if (key === storageKey && (opened || collection || bufferJob)) continue;
        let data;
        try { data = JSON.parse(localStorage.getItem(key)); } catch { continue; }
        if (!data || data.version !== 2 || key !== CACHE_PREFIX+data.article || !/^\/b\/[^/]+\/\d+$/.test(data.article) || !Array.isArray(data.comments)) continue;
        if (!data.comments.length && !data.pages?.length) continue;
        if (Number.isFinite(data.cacheTouchedAt) && now-data.cacheTouchedAt<CACHE_TTL) continue;
        // 시각이 없는 구버전 캐시도 정리하되 영상·싱크 설정은 유지합니다.
        localStorage.setItem(key,JSON.stringify({...data,comments:[],pages:[],cacheTouchedAt:now}));
        if (key === storageKey) { comments.clear(); pageCache.clear(); ordered = []; cacheTouchedAt = now; refresh(); }
      }
    } catch { /* 저장 접근 제한이 있으면 현재 메모리의 채팅은 유지합니다. */ }
  }
  function save() {
    cacheTouchedAt = Date.now();
    const value = JSON.stringify(exportData());
    try { localStorage.setItem(storageKey,value); }
    catch(e) {
      const quota = ['QuotaExceededError','NS_ERROR_DOM_QUOTA_REACHED'].includes(e?.name);
      if (quota) {
        cleanupCaches();
        try { localStorage.setItem(storageKey,value); return; } catch { /* 한 게시글 자체가 클 수 있습니다. */ }
      }
      status(quota ? '브라우저 댓글 캐시 저장 한도에 도달했습니다. 현재 채팅은 유지됩니다. 보관하려면 JSON으로 내보내세요.' : '브라우저에 댓글 캐시를 저장하지 못했습니다. 현재 채팅은 유지됩니다. 보관하려면 JSON으로 내보내세요.');
    }
  }
  function exportData() { return {version:2,article:articlePath,url:$('url').value,start,offset,endAt,manualEnd,endPreference,durationHint,syncReference:'end',cacheTouchedAt,comments:ordered,pages:[...pageCache.values()],maxPage}; }
  function syncFromEnd() {
    if (!manualEnd && endPreference === 'modified' && Number.isFinite(modifiedAt)) endAt = modifiedAt;
    const duration = ready && mode === 'youtube' ? player.getDuration() : durationHint;
    if (Number.isFinite(duration) && duration>0) {
      durationHint = duration;
      if (mode === 'youtube' || root.activeElement !== $('duration')) $('duration').value = duration;
    }
    const next = Number.isFinite(endAt) && durationHint>0 ? endAt-durationHint*1000 : NaN;
    if (!Object.is(next,start)) { start = next; lastRange = ''; }
    if (Number.isFinite(endAt) && root.activeElement !== $('end')) $('end').value = kstInput(endAt);
    $('modified').disabled = !Number.isFinite(modifiedAt);
    $('basis').textContent = manualEnd ? '직접 지정한 영상 끝 시각에 맞춥니다.' : endPreference === 'modified' && Number.isFinite(modifiedAt) ? '종료된 게시글의 수정일을 영상 끝에 맞춥니다.' : Number.isFinite(endAt) ? '마지막 댓글 시각을 영상 끝에 맞춘 임시 기준입니다. 방송 뒤 댓글이 있으면 수정하세요.' : '게시글 수정일과 끝 시각을 확인하는 중입니다.';
  }
  function refresh() {
    ordered = [...comments.values()].sort((a,b) => a.at-b.at || a.id.localeCompare(b.id,undefined,{numeric:true}));
    syncFromEnd();
    $('count').textContent = `${ordered.length.toLocaleString()}개`; lastRange = ''; render();
  }
  function absorb(doc, base, pageNumber = null) {
    if (new URL(base,articleURL).pathname === articlePath) articleMetadataChecked = true;
    const modified = modifiedDate(doc);
    if (Number.isFinite(modified)) modifiedAt = modified;
    const parsed = parseComments(doc,base);
    let added = 0;
    for (const c of parsed.comments) {
      const old = comments.get(c.id);
      if (!old) { comments.set(c.id,c); added++; }
      // 저장 HTML의 로컬 미디어 경로로 이미 확보한 CDN 주소를 덮어쓰지 않습니다.
      else if (c.media.length || !old.media.length) comments.set(c.id,c);
    }
    const id = detectVideo(doc);
    if (!$('url').value && id) $('url').value = `https://youtu.be/${id}`;
    const linked = commentPages(doc);
    if (linked.length) maxPage = Math.max(maxPage,...linked);
    if (pageNumber !== null) rememberPage(pageNumber,parsed.comments);
    refresh(); return {...parsed,added};
  }
  function rememberPage(number, rows) {
    const dates = rows.map(c => c.at);
    pageCache.set(number,{number,verified:true,ids:rows.map(c => c.id),first:dates.length ? Math.min(...dates) : null,last:dates.length ? Math.max(...dates) : null});
  }
  function restorePages(data) {
    if (Number.isInteger(data.maxPage) && data.maxPage >= 1 && data.maxPage <= 10000) maxPage = Math.max(maxPage,data.maxPage);
    if (!Array.isArray(data.pages)) return;
    for (const page of data.pages.slice(0,10000)) {
      // 이전 버전은 현재 DOM의 댓글을 1페이지라고 가정했습니다.
      // HTTP로 페이지 번호를 확인한 캐시만 복원하고 댓글 자체는 보존합니다.
      if (!page || page.verified !== true || !Number.isInteger(page.number) || page.number < 1 || page.number > 10000 || !Array.isArray(page.ids)) continue;
      if (!page.ids.every(id => typeof id === 'string' && comments.has(id))) continue;
      rememberPage(page.number,page.ids.map(id => comments.get(id)));
      maxPage = Math.max(maxPage,page.number);
    }
  }
  function render() {
    syncFromEnd(); $('clock').textContent = format(elapsed);
    if (root.activeElement !== $('seconds')) $('seconds').value = Math.floor(elapsed);
    const isPlaying = mode === 'youtube' ? ready && player.getPlayerState() === 1 : playing;
    $('play').textContent = isPlaying ? '일시정지' : '재생';
    const end = Number.isFinite(start) ? upperBound(start+(elapsed+offset)*1000) : 0;
    const begin = Math.max(0,end-150);
    const range = `${begin}:${end}`;
    $('shown').textContent = end ? `· ${end.toLocaleString()}번째까지` : '';
    if (range === lastRange) return;
    lastRange = range;
    const chat = $('chat'), messages = $('messages'), oldTop = chat.scrollTop;
    const anchorRow = [...messages.children].find(row => row.getBoundingClientRect().bottom >= chat.getBoundingClientRect().top);
    const anchorTop = anchorRow?.getBoundingClientRect().top;
    const existing = new Map([...messages.children].map(row => [row.dataset.id,row]));
    const fragment = document.createDocumentFragment();
    if (!end) {
      const hint = document.createElement('p'); hint.className = 'hint'; hint.textContent = ordered.length ? '이 재생 위치에 도착한 채팅이 없습니다.' : '게시글에 보존된 댓글을 불러오면 채팅이 나타납니다.'; fragment.append(hint);
    }
    for (let i=begin;i<end;i++) {
      const c = ordered[i];
      const reused = existing.get(c.id);
      if (reused && reused.commentData === c) { fragment.append(reused); continue; }
      const row = document.createElement('div'); row.className = 'message'; row.dataset.id = c.id; row.commentData = c;
      const stamp = document.createElement('span'); stamp.className = 'stamp'; stamp.textContent = c.at < start ? '시작 전' : format((c.at-start)/1000);
      const author = document.createElement('span'); author.className = 'author'; author.textContent = c.author;
      let hash = 0; for (const ch of c.identity) hash = (hash*31+ch.charCodeAt(0))|0;
      author.style.color = `hsl(${Math.abs(hash)%360} 65% 73%)`;
      const body = document.createElement('span'); body.className = 'body'; body.textContent = c.text;
      row.append(stamp,author,body);
      const arcacons = document.createElement('span'); arcacons.className = 'arcacons';
      for (const media of c.media) {
        const el = document.createElement(media.type === 'video' ? 'video' : 'img'); el.className = 'arcacon';
        if (media.type === 'video') { el.autoplay = true; el.loop = true; el.muted = true; el.playsInline = true; el.preload = 'none'; if (media.poster) el.poster = media.poster; }
        else { el.loading = 'lazy'; el.alt = '[아카콘]'; }
        el.referrerPolicy = 'no-referrer'; el.src = media.src;
        el.onload = el.onloadedmetadata = scheduleBottom;
        el.onerror = () => { const fallback = document.createElement('span'); fallback.className = 'missing'; fallback.textContent = '[아카콘]'; fallback.title = '아카콘을 불러오지 못했습니다.'; el.replaceWith(fallback); scheduleBottom(); };
        arcacons.append(el);
      }
      if (c.media.length) row.append(arcacons);
      if (c.missingMedia) { const span = document.createElement('span'); span.className = 'missing'; span.textContent = '[아카콘]'; span.title = '저장 HTML의 로컬 이미지입니다. 온라인 댓글을 다시 불러오면 원래 주소를 확보할 수 있습니다.'; row.append(span); }
      fragment.append(row);
    }
    messages.replaceChildren(fragment);
    if ($('follow').checked) scheduleBottom();
    else if (anchorRow?.isConnected) chat.scrollTop = oldTop+anchorRow.getBoundingClientRect().top-anchorTop;
    else chat.scrollTop = oldTop;
  }
  function snapshot() {
    const now = performance.now();
    if (mode === 'youtube' && ready) {
      const next = Math.max(0,player.getCurrentTime());
      const progress = player.getPlayerState() === 1 ? (now-anchor)/1000*rate : 0;
      if (Math.abs(next-elapsed-progress)>30) noticeSeek(next);
      elapsed = next;
    }
    else if (mode === 'timer' && playing) elapsed += (now-anchor)/1000*rate;
    anchor = now;
  }
  function timelineCached(at) {
    const pages = [...pageCache.values()].filter(p => p.first !== null).sort((a,b) => a.number-b.number);
    if (pages.some(p => p.first<=at && at<=p.last || p.number===1 && at<p.first || p.number===maxPage && at>p.last)) return true;
    return pages.some((p,i) => pages[i+1]?.number===p.number+1 && p.last<at && at<pages[i+1].first);
  }
  function noticeSeek(seconds) {
    seekPending = Number.isFinite(start) && !timelineCached(start+(seconds+offset)*1000);
    setBuffer(seekPending ? '채팅 버퍼링 중… · 이동한 위치의 채팅을 찾고 있습니다.' : '');
    retryAt = 0;
  }
  function jump(seconds) {
    if (!Number.isFinite(seconds)) return;
    snapshot();
    if (Math.abs(seconds-elapsed)>30) noticeSeek(Math.max(0,seconds));
    elapsed = Math.max(0,seconds);
    if (mode === 'youtube') { if (ready) player.seekTo(elapsed,true); else pendingSeek = elapsed; }
    lastRange = ''; render();
    retryAt = 0; ensureBuffer();
  }
  function loadAPI() {
    if (window.YT?.Player) return Promise.resolve();
    if (apiPromise) return apiPromise;
    apiPromise = new Promise((resolve,reject) => {
      const started = performance.now();
      const check = setInterval(() => {
        if (window.YT?.Player) { clearInterval(check); resolve(); }
        else if (performance.now()-started > 20000) { clearInterval(check); reject(new Error('YouTube API를 불러오지 못했습니다. 확장 프로그램의 차단 여부를 확인하세요.')); }
      },100);
      if (!document.querySelector('script[src="https://www.youtube.com/iframe_api"]')) {
        const script = document.createElement('script'); script.src = 'https://www.youtube.com/iframe_api'; document.head.append(script);
      }
    }).catch(e => { apiPromise = null; throw e; });
    return apiPromise;
  }
  async function loadVideo() {
    const id = youtubeID($('url').value);
    if (!id) { showSettings(); status('YouTube 영상 주소를 입력하세요.'); return; }
    const currentGeneration = ++generation;
    ready = false; playing = false; durationHint = 0; $('duration').value = '';
    if (player) { player.destroy(); player = null; }
    $('video-box').replaceChildren();
    const hint = document.createElement('div'); hint.id = 'placeholder'; hint.textContent = 'YouTube 플레이어를 준비하는 중…'; $('video-box').append(hint);
    try {
      await loadAPI();
      if (currentGeneration !== generation || !opened) return;
      const target = document.createElement('div'); $('video-box').replaceChildren(target);
      player = new window.YT.Player(target,{
        host:'https://www.youtube-nocookie.com',width:'100%',height:'100%',videoId:id,
        playerVars:{autoplay:0,playsinline:1,origin:location.origin,rel:0},
        events:{
          onReady(event) {
            if (currentGeneration !== generation) return;
            ready = true;
            if (pendingSeek !== null) { event.target.seekTo(pendingSeek,true); pendingSeek = null; }
            if (!opened) event.target.pauseVideo();
            status('영상 끝 시각을 기준으로 채팅이 따라갑니다.'); render(); save();
          },
          onError(event) { if (currentGeneration === generation) { ready = false; status(`YouTube 오류 ${event.data}: 비공개·삭제·임베드 제한 여부를 확인하세요. 별도 타이머로도 채팅을 재생할 수 있습니다.`); } },
          onPlaybackRateChange(event) { if (currentGeneration === generation) { rate = event.data; $('rate').value = String(rate); } }
        }
      }); save();
    } catch(e) { if (currentGeneration === generation) status(e.message); }
  }
  function checkAbort(signal) { if (signal.aborted) throw new DOMException('중지됨','AbortError'); }
  function waitRequest(ms, signal) {
    return new Promise((resolve,reject) => {
      function abort() { clearTimeout(timer); signal.removeEventListener('abort',abort); reject(new DOMException('중지됨','AbortError')); }
      const timer = setTimeout(() => { signal.removeEventListener('abort',abort); resolve(); },Math.max(0,ms));
      signal.addEventListener('abort',abort,{once:true}); if (signal.aborted) abort();
    });
  }
  async function fetchPage(number, controller, force = false) {
    checkAbort(controller.signal);
    if (!force && pageCache.has(number)) return pageCache.get(number);
    if (seekPending && !collection && bufferJob?.phase === 'locating') setBuffer('채팅 버퍼링 중… · 이동한 위치의 채팅을 찾고 있습니다.');
    await waitRequest(REQUEST_GAP-(performance.now()-lastRequestAt),controller.signal);
    checkAbort(controller.signal);
    const url = new URL(articleURL); url.searchParams.set('cp',String(number));
    lastRequestAt = performance.now();
    const timeout = setTimeout(() => controller.abort(),20000);
    try {
      const response = await fetch(url,{credentials:'same-origin',signal:controller.signal});
      if (!response.ok) throw new Error(`댓글 요청 실패: HTTP ${response.status}`);
      const finalURL = new URL(response.url);
      if (finalURL.origin !== articleURL.origin || finalURL.pathname !== articlePath) throw new Error('로그인 또는 접근 제한으로 게시글을 읽지 못했습니다.');
      const text = await response.text(); checkAbort(controller.signal);
      const doc = new DOMParser().parseFromString(text,'text/html');
      if (!doc.querySelector('#comment, .article-comment')) throw new Error('댓글 영역을 찾지 못했습니다. 로그인/접근 제한 또는 사이트 구조를 확인하세요.');
      absorb(doc,url.href,number); save();
      return pageCache.get(number);
    } finally { clearTimeout(timeout); }
  }
  async function locatePage(target, controller) {
    // 시작 구간부터 확인해 첫 실행에서 불필요한 중간 페이지 탐색을 피합니다.
    if (!pageCache.has(1)) await fetchPage(1,controller);
    // 댓글 페이지는 중계 중 작성된 순서대로 시간 범위가 이어집니다.
    // 캐시 범위로 좁힌 뒤 먼 탐색에는 이진 탐색을 사용합니다.
    for (let expansion=0;expansion<20;expansion++) {
      let lo = 1, hi = maxPage;
      for (const page of pageCache.values()) {
        if (page.first === null) continue;
        if (page.first <= target && target <= page.last) return page.number;
        if (page.last < target) lo = Math.max(lo,page.number+1);
        else if (page.first > target) hi = Math.min(hi,page.number);
      }
      if (lo > maxPage) {
        const boundary = await fetchPage(maxPage,controller);
        if (boundary.number < maxPage) continue; // 마지막 링크에서 더 뒤의 페이지를 발견한 경우
        return maxPage;
      }
      hi = Math.max(lo,hi);
      while (lo < hi) {
        const mid = Math.floor((lo+hi)/2), page = await fetchPage(mid,controller);
        if (page.last === null) throw new Error(`${mid}페이지의 댓글 시각을 확인할 수 없습니다.`);
        if (page.last < target) lo = mid+1; else hi = mid;
      }
      const page = await fetchPage(lo,controller);
      if (page.last !== null && page.last < target && lo < maxPage) continue;
      return lo;
    }
    throw new Error('해당 시간의 댓글 페이지를 찾지 못했습니다. 영상 끝 시각을 확인하세요.');
  }
  async function lastPageEnd(controller) {
    for (let tries=0;tries<20;tries++) {
      const page = await fetchPage(maxPage,controller);
      if (page.number < maxPage) continue;
      if (page.last === null) throw new Error('마지막 댓글 시각을 읽지 못했습니다. 설정에서 영상 끝 시각을 직접 지정하세요.');
      return page.last;
    }
    throw new Error('마지막 페이지를 찾지 못했습니다. 설정에서 영상 끝 시각을 직접 지정하세요.');
  }
  function ensureBuffer() {
    if (!opened || collection || performance.now() < retryAt) return;
    const target = Number.isFinite(start) ? start+(elapsed+offset)*1000 : null;
    if (bufferJob) { if (target !== null && bufferJob.target !== null && Math.abs(target-bufferJob.target)>30000) bufferJob.controller.abort(); return; }
    const job = {controller:new AbortController(),target,promise:null,phase:'locating'}; bufferJob = job;
    job.promise = (async () => {
      try {
        if (!manualEnd && endPreference === 'modified' && !articleMetadataChecked) await fetchPage(1,job.controller,true);
        if (!Number.isFinite(endAt)) {
          const candidate = await lastPageEnd(job.controller);
          if (!manualEnd) { endAt = candidate; syncFromEnd(); save(); }
        }
        syncFromEnd();
        if (!Number.isFinite(start)) return;
        const at = start+(elapsed+offset)*1000;
        job.target = at;
        const center = await locatePage(at,job.controller);
        checkAbort(job.controller.signal);
        seekPending = false; setBuffer('');
        job.phase = 'prefetch';
        // 한 구간당 중심 페이지와 최대 앞뒤 두 페이지만 읽습니다.
        // 채팅 밀도가 높아도 정지된 타임라인에서 끝까지 수집하지 않습니다.
        const current = pageCache.get(center);
        let edge = current;
        for (let n=center-1;n>=Math.max(1,center-2) && edge.first !== null && edge.first>at-BEHIND;n--) edge = await fetchPage(n,job.controller);
        edge = current;
        for (let n=center+1;n<=Math.min(maxPage,center+2) && edge.last !== null && edge.last<at+AHEAD*Math.max(1,rate);n++) edge = await fetchPage(n,job.controller);
      } catch(e) {
        if (!job.controller.signal.aborted || opened && (job.target === null || Math.abs(job.target-(start+(elapsed+offset)*1000))<30000)) {
          retryAt = performance.now()+30000;
          if (seekPending) setBuffer('채팅 찾기 지연 · 설정에서 다시 확인',false);
          status(e.message || '댓글 요청이 중지되거나 시간 초과되었습니다.');
        }
      } finally { if (bufferJob === job) bufferJob = null; }
    })();
  }
  async function collectAll() {
    if (collection) { collection.abort(); return; }
    seekPending = false; setBuffer('');
    const controller = new AbortController(); collection = controller;
    $('collect').textContent = '불러오기 중지';
    try {
      if (bufferJob) { bufferJob.controller.abort(); await bufferJob.promise; }
      for (let number=1;number<=maxPage;number++) {
        if (number>500) throw new Error('500페이지에서 중지했습니다.');
        status(`보관용 댓글 ${number}/${maxPage}페이지 읽는 중…`);
        await fetchPage(number,controller);
      }
      status(`전체 보관 완료 · ${comments.size.toLocaleString()}개`);
    } catch(e) { status(controller.signal.aborted ? '보관용 수집을 중지했습니다. 읽은 댓글은 보관했습니다.' : e.message); }
    finally { collection = null; $('collect').textContent = '전체 댓글 보관'; setBuffer(''); save(); }
  }
  function validate(data) {
    if (data.version !== 2 || data.article !== articlePath || !Array.isArray(data.comments) || data.comments.length > 100000) throw new Error('이 게시글의 v2 다시 보기 파일이 아닙니다.');
    const clean = data.comments.map(c => {
      if (!c || typeof c.id !== 'string' || !Number.isFinite(c.at) || !Number.isFinite(new Date(c.at).getTime()) || typeof c.author !== 'string' || typeof c.text !== 'string') throw new Error('댓글 데이터 오류');
      const media = Array.isArray(c.media) ? c.media.slice(0,20).map(m => ({type:m?.type,src:safeMedia(m?.src,articleURL),poster:safeMedia(m?.poster,articleURL)})).filter(m => ['image','video'].includes(m.type) && m.src) : [];
      return {id:c.id,at:c.at,author:c.author,identity:typeof c.identity === 'string' ? c.identity : c.author,text:c.text,media,missingMedia:!!c.missingMedia};
    });
    return {comments:clean,offset:data.syncReference === 'end' && Number.isFinite(data.offset) ? data.offset : 0,url:youtubeID(data.url) ? data.url : '',endAt:data.syncReference === 'end' && Number.isFinite(data.endAt) && Number.isFinite(new Date(data.endAt).getTime()) ? data.endAt : NaN,manualEnd:data.syncReference === 'end' && !!data.manualEnd,endPreference:data.endPreference === 'last-comment' ? 'last-comment' : 'modified',durationHint:Number.isFinite(data.durationHint) && data.durationHint>0 ? data.durationHint : 0,pages:data.pages,maxPage:data.maxPage};
  }
  function open() {
    if (opened) return;
    opened = true; previousOverflow = document.documentElement.style.overflow; document.documentElement.style.overflow = 'hidden';
    $('overlay').hidden = false; $('launch').hidden = true; anchor = performance.now();
    if (!player && youtubeID($('url').value)) loadVideo();
    else if (!youtubeID($('url').value)) { showSettings(); status('영상 주소를 찾지 못했습니다. YouTube 주소를 입력하세요.'); }
    retryAt = 0; ensureBuffer();
    render();
  }
  function close() {
    if (!opened) return;
    snapshot(); playing = false; if (ready) player.pauseVideo();
    opened = false; $('overlay').hidden = true; $('launch').hidden = false;
    seekPending = false; setBuffer('');
    hideSettings();
    bufferJob?.controller.abort(); collection?.abort();
    document.documentElement.style.overflow = previousOverflow; save();
  }
  $('launch').onclick = open; $('close').onclick = close;
  document.addEventListener('keydown',e => { if (e.key === 'Escape' && opened) { if (!$('settings').hidden) hideSettings(); else close(); } });
  root.addEventListener('keydown',e => {
    if (e.key !== 'Tab' || $('settings').hidden) return;
    const focusable = [...$('settings').querySelectorAll('button,input,select,a[href]')].filter(el => !el.disabled && el.getClientRects().length);
    const index = focusable.indexOf(root.activeElement);
    if (e.shiftKey && index<=0) { e.preventDefault(); focusable.at(-1)?.focus(); }
    else if (!e.shiftKey && index===focusable.length-1) { e.preventDefault(); focusable[0]?.focus(); }
  });
  $('collect').onclick = collectAll; $('load-video').onclick = loadVideo;
  $('retry').onclick = () => { retryAt = 0; ensureBuffer(); };
  $('end').onchange = () => { const value = parseDate($('end').value); if (!Number.isFinite(value)) return; endAt = value; manualEnd = true; refresh(); save(); retryAt = 0; ensureBuffer(); };
  $('duration').onchange = () => { const value = Number($('duration').value); if (mode !== 'timer' || !Number.isFinite(value) || value<=0) return; durationHint = value; refresh(); save(); retryAt = 0; ensureBuffer(); };
  $('offset').onchange = () => { const value = Number($('offset').value); if (Number.isFinite(value)) { offset = value; lastRange = ''; render(); save(); retryAt = 0; ensureBuffer(); } };
  $('last').onclick = () => { endPreference = 'last-comment'; manualEnd = false; endAt = NaN; retryAt = 0; bufferJob?.controller.abort(); syncFromEnd(); save(); ensureBuffer(); };
  $('modified').onclick = () => { endPreference = 'modified'; manualEnd = false; retryAt = 0; bufferJob?.controller.abort(); refresh(); save(); ensureBuffer(); };
  $('play').onclick = () => {
    if (!Number.isFinite(start)) { showSettings(); status('영상 끝 시각과 전체 길이를 먼저 확인하세요.'); return; }
    snapshot();
    if (mode === 'youtube') { if (!ready) { status('영상이 아직 준비되지 않았습니다. 영상 설정 또는 별도 타이머를 확인하세요.'); return; } player.getPlayerState() === 1 ? player.pauseVideo() : player.playVideo(); }
    else playing = !playing;
    render();
  };
  $('mode').onchange = () => { snapshot(); if (ready) player.pauseVideo(); mode = $('mode').value; playing = false; anchor = performance.now(); $('timer-controls').hidden = mode !== 'timer'; $('duration').readOnly = mode === 'youtube'; if (mode === 'youtube' && ready) player.seekTo(elapsed,true); status(mode === 'timer' ? '별도 타이머입니다. 영상 전체 길이와 외부 영상의 재생 위치를 직접 맞춰주세요.' : 'YouTube 재생 위치에 동기화합니다.'); render(); };
  $('rate').onchange = () => { snapshot(); rate = Number($('rate').value); if (ready && mode === 'youtube') { const available = player.getAvailablePlaybackRates(); if (!available.includes(rate)) { rate = player.getPlaybackRate(); $('rate').value = String(rate); status('이 영상은 선택한 배속을 지원하지 않습니다.'); } else player.setPlaybackRate(rate); } };
  $('reset').onclick = () => jump(0); $('jump').onclick = () => jump(Number($('seconds').value));
  $('follow').onchange = scheduleBottom;
  $('export').onclick = () => {
    if (objectURL) URL.revokeObjectURL(objectURL);
    objectURL = URL.createObjectURL(new Blob([JSON.stringify(exportData(),null,2)],{type:'application/json'}));
    const link = document.createElement('a'); link.href = objectURL; link.download = `arca-${path[2]}-replay.json`; link.click();
  };
  $('import').onclick = () => $('file').click();
  $('file').onchange = async () => {
    let imported = 0, missing = 0;
    try {
      for (const file of $('file').files) {
        if (file.size > 30*1024*1024) throw new Error('파일당 크기 제한은 30MB입니다.');
        const text = await file.text();
        if (/\.html?$/i.test(file.name)) {
          const doc = new DOMParser().parseFromString(text,'text/html');
          const canonical = doc.querySelector('link[rel="canonical"]')?.getAttribute('href');
          if (!canonical || new URL(canonical).pathname !== articlePath) throw new Error('다른 게시글의 HTML은 가져올 수 없습니다.');
          const parsed = absorb(doc,articleURL.href); imported += parsed.added; missing += parsed.missingMedia;
          if (!parsed.comments.length) status('이 HTML에는 작성 시각이 있는 댓글이 없습니다. /b/ 일반 게시글을 저장하세요.');
        } else {
          const data = validate(JSON.parse(text));
          data.comments.forEach(c => { if (!comments.has(c.id)) imported++; comments.set(c.id,c); });
          endAt = data.endAt; manualEnd = data.manualEnd; endPreference = data.endPreference; durationHint = data.durationHint; offset = data.offset; if (data.url) $('url').value = data.url;
          restorePages(data);
          $('offset').value = offset; refresh();
        }
      }
      save(); status(`새 댓글 ${imported}개 가져왔습니다.${missing ? ' 저장 HTML의 로컬 아카콘 '+missing+'개는 온라인 댓글 수집으로 복원할 수 있습니다.' : ''}`);
      if (opened && !player && youtubeID($('url').value)) loadVideo();
    } catch(e) { refresh(); save(); status(`가져오기 실패: ${e.message}`); }
    $('file').value = '';
  };
  $('clear').onclick = () => {
    if (collection || bufferJob) { status('댓글을 읽고 있습니다. 잠시 후 초기화하세요.'); return; }
    if (!confirm('이 게시글에서 수집한 다시 보기 댓글을 초기화할까요?')) return;
    comments.clear(); pageCache.clear(); ordered = []; playing = false; if (ready) player.pauseVideo(); lastRange = ''; refresh(); save(); status('수집한 댓글을 초기화했습니다.');
  };
  cleanupCaches();
  try {
    const saved = localStorage.getItem(storageKey);
    if (saved) { const data = validate(JSON.parse(saved)); data.comments.forEach(c => comments.set(c.id,c)); endAt = data.endAt; manualEnd = data.manualEnd; endPreference = data.endPreference; durationHint = data.durationHint; offset = data.offset; $('url').value = data.url; $('offset').value = offset; restorePages(data); }
  } catch { status('이전에 저장한 데이터를 읽지 못했습니다.'); }
  // 페이지의 댓글은 기본 정렬이나 AJAX 갱신으로 URL의 cp와 다를 수 있습니다.
  // 즉시 표시용으로 읽되, 정규화한 cp 요청 응답만 페이지 탐색 캐시로 씁니다.
  absorb(document,location.href); save();
  setInterval(() => { if (opened) { snapshot(); render(); ensureBuffer(); } },200);
  setInterval(() => { if (opened || collection) save(); cleanupCaches(); },60000);
  window.addEventListener('pagehide',() => { collection?.abort(); bufferJob?.controller.abort(); chatResize.disconnect(); if (objectURL) URL.revokeObjectURL(objectURL); });
})();
