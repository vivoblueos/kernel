"use strict";

(() => {
    const picker = document.querySelector(".language-picker");
    if (!picker) return;

    const languageRoot = new URL(picker.dataset.root, window.location.href);
    const bookRoot = picker.dataset.language === "zh"
        ? new URL("../", languageRoot)
        : languageRoot;
    const page = picker.dataset.page.replace(/\.md$/, ".html") || "index.html";

    for (const link of picker.querySelectorAll("a[hreflang]")) {
        const path = link.hreflang === "zh" ? `zh/${page}` : page;
        link.href = new URL(path, bookRoot).href;
    }

    const toolbar = document.querySelector(".menu-bar .right-buttons");
    if (toolbar) toolbar.prepend(picker);

    const button = picker.querySelector("button");
    const menu = picker.querySelector(".language-menu");
    const setOpen = (open) => {
        menu.hidden = !open;
        button.setAttribute("aria-expanded", String(open));
    };

    setOpen(false);
    picker.classList.add("dropdown");
    button.hidden = false;
    button.addEventListener("click", () => setOpen(menu.hidden));
    document.addEventListener("click", (event) => {
        if (!picker.contains(event.target)) setOpen(false);
    });
    document.addEventListener("keydown", (event) => {
        if (event.key === "Escape" && !menu.hidden) {
            setOpen(false);
            button.focus();
        }
    });
    picker.addEventListener("focusout", (event) => {
        if (!picker.contains(event.relatedTarget)) setOpen(false);
    });
})();
