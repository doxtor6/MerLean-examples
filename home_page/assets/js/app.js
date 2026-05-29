/**
 * MerLean — Modern SPA Application Logic
 */

/* ---- Blog Data ---- */
const blogPosts = [
  {
    file:    "blog2.md",
    title:   "MerLean-Prover and Its Performance on FormalQualBench",
    date:    "2026-05-27",
    excerpt: "MerLean-Prover now closes 10/23 FormalQualBench problems and 12/12 on a Putnam 2025 slice, using a recursive Lean proof harness without fine-tuning."
  },
  {
    file:    "blog1.md",
    title:   "Formalizing Balanced Product Quantum Codes with MerLean",
    date:    "2026-03-14",
    excerpt: "We evaluated MerLean on one of the most important papers in Quantum Error Correction — here's how the dual-engine architecture handled it and what we learned."
  }
];

/* ---- Tab Switching ---- */
function switchTab(tabName) {
  // Update nav
  document.querySelectorAll('.nav-tab').forEach(btn => btn.classList.remove('active'));
  const navBtn = document.querySelector(`[data-tab="${tabName}"]`);
  if (navBtn) navBtn.classList.add('active');

  // Update content
  document.querySelectorAll('.tab-content').forEach(el => el.classList.remove('active'));
  const tabEl = document.getElementById('tab-' + tabName);
  if (tabEl) tabEl.classList.add('active');

  // Reset blog view if switching to blogs
  if (tabName === 'blogs') {
    closeBlogPost();
  }

  // Update URL hash
  window.location.hash = tabName === 'home' ? '' : tabName;

  // Scroll to top
  window.scrollTo({ top: 0, behavior: 'smooth' });
}

/* ---- Blog Rendering ---- */
function formatDate(dateStr) {
  const d = new Date(dateStr + "T00:00:00");
  return d.toLocaleDateString("en-US", { year: "numeric", month: "long", day: "numeric" });
}

function renderBlogList() {
  const container = document.getElementById("blog-list");
  if (!container) return;

  const sorted = blogPosts.slice().sort((a, b) => b.date.localeCompare(a.date));

  container.innerHTML = sorted.map(post => `
    <div class="blog-card" onclick="openBlogPost('${post.file}', '${post.title.replace(/'/g, "\\'")}', '${post.date}')">
      <div class="blog-date">${formatDate(post.date)}</div>
      <div class="blog-card-title">${post.title}</div>
      <div class="blog-card-excerpt">${post.excerpt}</div>
      <span class="blog-read-more">Read more →</span>
    </div>
  `).join('');
}

function openBlogPost(file, title, date) {
  document.getElementById('blog-list-view').style.display = 'none';
  document.getElementById('blog-post-view').classList.add('active');
  document.getElementById('blog-post-title').textContent = title;
  document.getElementById('blog-post-date').textContent = formatDate(date);

  const bodyEl = document.getElementById('blog-post-body');
  bodyEl.innerHTML = '<p style="color:var(--text-muted)">Loading...</p>';

  fetch('blogs/' + file)
    .then(res => {
      if (!res.ok) throw new Error('Not found');
      return res.text();
    })
    .then(md => {
      bodyEl.innerHTML = marked.parse(md);
    })
    .catch(() => {
      bodyEl.innerHTML = '<p>Could not load post.</p>';
    });
}

function closeBlogPost() {
  document.getElementById('blog-list-view').style.display = 'block';
  document.getElementById('blog-post-view').classList.remove('active');
}

/* ---- BibTeX Copy ---- */
function copyBibtex() {
  const bibtex = document.querySelector('.bibtex-block').textContent
    .replace('Copy', '').trim();
  navigator.clipboard.writeText(bibtex).then(() => {
    const btn = document.getElementById('copy-bibtex-btn');
    btn.textContent = 'Copied!';
    setTimeout(() => { btn.textContent = 'Copy'; }, 2000);
  });
}

/* ---- Init ---- */
document.addEventListener('DOMContentLoaded', () => {
  // Tab click handlers
  document.querySelectorAll('.nav-tab').forEach(btn => {
    btn.addEventListener('click', () => switchTab(btn.dataset.tab));
  });

  // Render blog list
  renderBlogList();

  // Handle initial hash
  const hash = window.location.hash.replace('#', '');
  if (hash && document.getElementById('tab-' + hash)) {
    switchTab(hash);
  }
});

// Handle back/forward navigation
window.addEventListener('hashchange', () => {
  const hash = window.location.hash.replace('#', '') || 'home';
  if (document.getElementById('tab-' + hash)) {
    switchTab(hash);
  }
});
