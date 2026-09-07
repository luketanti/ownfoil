import re
import unittest
from pathlib import Path

from jinja2 import ChainableUndefined, DictLoader, Environment
from test_users_templates import ModalLocationParser


class OverlayLayerTests(unittest.TestCase):
    def test_shared_content_layer_excludes_bootstrap_overlays(self):
        css = (Path(__file__).resolve().parents[1] / 'app/static/style.css').read_text()
        selector = re.search(r'body > [^{]+', css).group()
        for overlay in ('modal', 'modal-backdrop', 'tooltip', 'popover',
                        'dropdown-menu', 'offcanvas', 'offcanvas-backdrop'):
            with self.subTest(overlay=overlay):
                self.assertIn(f':not(.{overlay})', selector)

    def test_rendered_modal_pages_keep_dialogs_at_content_root(self):
        templates = Path(__file__).resolve().parents[1] / 'app/templates'
        sources = {'base.html': '{% block content %}{% endblock %}', 'nav.html': ''}
        for name in ('index.html', 'manage.html', 'requests.html', 'settings.html', 'users.html'):
            markup = (templates / name).read_text().split('<script')[0]
            if '{% endblock %}' not in markup:
                markup += '{% endblock %}'
            sources[name] = markup
        env = Environment(loader=DictLoader(sources), undefined=ChainableUndefined)
        for admin in (False, True):
            for name in sources.keys() - {'base.html', 'nav.html'}:
                markup = env.get_template(name).render(
                    current_user={'is_admin': admin}, admin_account_created=True,
                    url_for=lambda *args, **kwargs: '', download_ui_visibility={})
                parser = ModalLocationParser()
                parser.feed(markup)
                for modal, ancestors in parser.modals.items():
                    with self.subTest(page=name, admin=admin, modal=modal):
                        self.assertEqual(ancestors, [])
