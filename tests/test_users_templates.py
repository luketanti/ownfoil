import unittest
from html.parser import HTMLParser
from pathlib import Path


class ModalLocationParser(HTMLParser):
    VOID_TAGS = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input',
                 'link', 'meta', 'param', 'source', 'track', 'wbr'}

    def __init__(self):
        super().__init__()
        self.parents = []
        self.modals = {}

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'modal' in attrs.get('class', '').split():
            self.modals[attrs.get('id')] = list(self.parents)
        if tag not in self.VOID_TAGS:
            self.parents.append(tag)

    def handle_endtag(self, tag):
        if tag in self.parents:
            index = len(self.parents) - 1 - self.parents[::-1].index(tag)
            del self.parents[index:]


class UsersTemplateTests(unittest.TestCase):
    def test_account_modals_are_outside_page_stacking_context(self):
        template = Path(__file__).resolve().parents[1] / 'app/templates/users.html'
        parser = ModalLocationParser()
        parser.feed(template.read_text(encoding='utf-8'))
        expected = {'deleteUserModal', 'editUserModal', 'resetPasswordModal',
                    'freezeUserModal', 'userHistoryModal'}
        self.assertEqual(set(parser.modals), expected)
        for modal_id, parents in parser.modals.items():
            with self.subTest(modal=modal_id):
                self.assertEqual(parents, [], 'Modal must be at content-block root')


if __name__ == '__main__':
    unittest.main()
