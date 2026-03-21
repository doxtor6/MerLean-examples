/**
 * MerLean Blog — post listing and rendering.
 *
 * To add a new post:
 *   1. Create a Markdown file in the blogs/ folder (e.g. 2026-04-01-my-post.md)
 *   2. Add an entry to the blogPosts array below.
 */

const blogPosts = [
  {
    file:    "blog2.md",
    title:   "MerLean-prover and Its Performance on FormalQualBench",
    date:    "2026-03-21",
    excerpt: "MerLean-prover solves 8 out of 8 graduate-level FormalQualBench problems at 100% success rate — all 82 statements with no axioms and no sorry."
  },
  {
    file:    "blog1.md",
    title:   "Formalizing Balanced Product Quantum Codes with MerLean",
    date:    "2026-03-14",
    excerpt: "We evaluated MerLean on one of the most important papers in Quantum Error Correction — here's how the dual-engine architecture handled it and what we learned."
  }
];

function formatDate(dateStr) {
  const d = new Date(dateStr + "T00:00:00");
  return d.toLocaleDateString("en-US", { year: "numeric", month: "long", day: "numeric" });
}

function loadBlogPosts() {
  const container = document.getElementById("blog-list");
  if (!container) return;

  if (blogPosts.length === 0) {
    container.innerHTML = '<p class="blog-empty">No blog posts yet. Stay tuned!</p>';
    return;
  }

  // Sort newest first
  const sorted = blogPosts.slice().sort((a, b) => b.date.localeCompare(a.date));

  container.innerHTML = sorted
    .map(
      (post) => `
    <article class="blog-card">
      <a href="blog-post.html?post=${encodeURIComponent(post.file)}" class="blog-card-link">
        <time class="blog-date">${formatDate(post.date)}</time>
        <h3 class="blog-card-title">${post.title}</h3>
        <p class="blog-card-excerpt">${post.excerpt}</p>
        <span class="blog-read-more">Read more &rarr;</span>
      </a>
    </article>`
    )
    .join("");
}

document.addEventListener("DOMContentLoaded", loadBlogPosts);
