import shutil
import subprocess
import unittest
from pathlib import Path


class LibraryImageTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('node'), 'Node.js is required for browser logic tests')
    def test_viewport_loading_and_reset(self):
        script = Path(__file__).resolve().parents[1] / 'app/static/library-images.js'
        harness = r"""
const assert = require('node:assert/strict');
const vm = require('node:vm');
const fs = require('node:fs');
let callback, options, disconnected = 0;
const observed = new Set();
class Observer {
    constructor(cb, opts) { callback = cb; options = opts; }
    observe(image) { observed.add(image); }
    unobserve(image) { observed.delete(image); }
    disconnect() { observed.clear(); disconnected++; }
}
const context = {window: {IntersectionObserver: Observer}, IntersectionObserver: Observer};
vm.createContext(context);
vm.runInContext(fs.readFileSync(process.argv[1], 'utf8'), context);
const loader = context.window.libraryImages;
const images = Array.from({length: 1000}, (_, i) => ({dataset: {librarySrc: `/image/${i}`}, src: 'placeholder'}));
const root = {querySelectorAll: () => images.filter(i => i.dataset.librarySrc)};
loader.observe(root);
assert.equal(observed.size, 1000);
assert.ok(images.every(i => i.src === 'placeholder'));
assert.equal(options.rootMargin, '240px');
callback([{target: images[0], isIntersecting: false}]);
assert.equal(images[0].src, 'placeholder');
callback([{target: images[0], isIntersecting: true}]);
assert.equal(images[0].src, '/image/0');
assert.equal(images[0].dataset.librarySrc, undefined);
assert.equal(observed.size, 999);
assert.ok(images.slice(1).every(i => i.src === 'placeholder'));
loader.reset();
assert.equal(disconnected, 1);
assert.equal(observed.size, 0);
loader.observe(root);
assert.equal(observed.size, 999);
delete context.window.IntersectionObserver;
loader.reset();
loader.observe(root);
assert.ok(images.every((image, i) => image.src === `/image/${i}`));
"""
        subprocess.run(['node', '-e', harness, str(script)], check=True)

    def test_library_wires_deferred_artwork_and_bounded_placeholders(self):
        template = (Path(__file__).resolve().parents[1] / 'app/templates/index.html').read_text()
        self.assertIn("filename='library-images.js'", template)
        self.assertEqual(template.count('data-library-src'), 3)
        self.assertIn('const count = Math.min(24,', template)
        self.assertIn("libraryImages.observe(document.getElementById('gameGrid'))", template)
        self.assertIn("libraryImages.observe(document.getElementById('discoverSection'))", template)


if __name__ == '__main__':
    unittest.main()
