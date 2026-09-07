/* Keep remote artwork requests close to the visible portion of the library. */
window.libraryImages = (() => {
    let observer;

    function load(image) {
        const source = image.dataset.librarySrc;
        if (!source) return;
        delete image.dataset.librarySrc;
        image.src = source;
    }

    function reset() {
        if (observer) observer.disconnect();
    }

    function observe(root) {
        const images = root.querySelectorAll('img[data-library-src]');
        if (!('IntersectionObserver' in window)) {
            images.forEach(load); // Native loading="lazy" remains the fallback.
            return;
        }
        if (!observer) {
            observer = new IntersectionObserver(entries => {
                entries.forEach(entry => {
                    if (!entry.isIntersecting) return;
                    observer.unobserve(entry.target);
                    load(entry.target);
                });
            }, { rootMargin: '240px', threshold: 0 });
        }
        images.forEach(image => observer.observe(image));
    }

    return { reset, observe };
})();
