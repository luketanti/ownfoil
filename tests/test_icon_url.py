import unittest
import sys
import os
from unittest.mock import Mock, patch, MagicMock

# Add app directory to path
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(__file__)), 'app'))


class TestIconUrlGeneration(unittest.TestCase):
    """Test that library generation uses local proxy endpoint for icons"""

    @patch('library.titles_lib')
    @patch('library.get_all_apps')
    @patch('library.get_title')
    @patch('library.get_all_title_apps')
    @patch('library.save_library_to_disk')
    @patch('library.is_library_unchanged')
    @patch('library.compute_apps_hash')
    def test_generate_library_uses_local_icon_proxy(
        self, mock_hash, mock_unchanged, mock_save, mock_get_all_title_apps, 
        mock_get_title, mock_get_all_apps, mock_titles_lib
    ):
        """Test that iconUrl points to local proxy endpoint"""
        import library
        from library import generate_library
        
        # Mock library unchanged check
        mock_unchanged.return_value = False
        mock_hash.return_value = 'test_hash'
        
        # Mock titledb loading
        mock_titles_lib.load_titledb = Mock()
        mock_titles_lib.identification_in_progress_count = 0
        mock_titles_lib.unload_titledb = Mock()
        
        # Mock a BASE game
        mock_get_all_apps.return_value = [
            {
                'title_id': '0100000000010000',
                'app_id': '0100000000010000',
                'app_type': 'BASE',
                'app_version': '0',
            }
        ]
        
        # Mock titledb info with CDN URL
        mock_titles_lib.get_game_info.return_value = {
            'name': 'Test Game',
            'bannerUrl': 'https://cdn.example.com/banner.jpg',
            'iconUrl': 'https://cdn.example.com/icon.jpg',  # Direct CDN URL
            'id': '0100000000010000',
            'category': 'Game',
        }
        
        # Mock title object
        mock_title_obj = Mock()
        mock_title_obj.have_base = True
        mock_title_obj.up_to_date = True
        mock_title_obj.complete = True
        mock_get_title.return_value = mock_title_obj
        
        # Mock title apps (no updates)
        mock_get_all_title_apps.return_value = []
        
        # Mock versions
        mock_titles_lib.get_all_existing_versions.return_value = []
        
        # Generate library
        library = generate_library()
        
        # Verify iconUrl uses local proxy endpoint
        self.assertEqual(len(library), 1)
        game = library[0]
        self.assertEqual(game['iconUrl'], '/api/shop/icon/0100000000010000')
        
        # Verify other fields are preserved
        self.assertEqual(game['name'], 'Test Game')
        self.assertEqual(game['title_id'], '0100000000010000')

    @patch('library.titles_lib')
    @patch('library.get_all_apps')
    @patch('library.get_all_title_apps')
    @patch('library.save_library_to_disk')
    @patch('library.is_library_unchanged')
    @patch('library.compute_apps_hash')
    def test_generate_library_dlc_uses_local_icon_proxy(
        self, mock_hash, mock_unchanged, mock_save, mock_get_all_title_apps, 
        mock_get_all_apps, mock_titles_lib
    ):
        """Test that DLC iconUrl points to base game's icon via local proxy"""
        import library
        from library import generate_library
        
        # Mock library unchanged check
        mock_unchanged.return_value = False
        mock_hash.return_value = 'test_hash'
        
        # Mock titledb loading
        mock_titles_lib.load_titledb = Mock()
        mock_titles_lib.identification_in_progress_count = 0
        mock_titles_lib.unload_titledb = Mock()
        
        # Mock a DLC
        mock_get_all_apps.return_value = [
            {
                'title_id': '0100000000010000',  # Base game title_id
                'app_id': '0100000000010001',    # DLC app_id
                'app_type': 'DLC',
                'app_version': '0',
            }
        ]
        
        # Mock titledb info for DLC
        def mock_get_game_info(app_id):
            if app_id == '0100000000010001':  # DLC
                return {
                    'name': 'Test DLC',
                    'bannerUrl': 'https://cdn.example.com/dlc_banner.jpg',
                    'iconUrl': 'https://cdn.example.com/dlc_icon.jpg',
                    'id': '0100000000010001',
                    'category': 'DLC',
                }
            elif app_id == '0100000000010000':  # Base game
                return {
                    'name': 'Test Game',
                    'bannerUrl': 'https://cdn.example.com/banner.jpg',
                    'iconUrl': 'https://cdn.example.com/icon.jpg',
                    'id': '0100000000010000',
                    'category': 'Game',
                }
            return None
        
        mock_titles_lib.get_game_info.side_effect = mock_get_game_info
        
        # Mock title apps (no other versions)
        mock_get_all_title_apps.return_value = [
            {
                'app_id': '0100000000010001',
                'app_type': 'DLC',
                'app_version': '0',
                'owned': True,
            }
        ]
        
        # Generate library
        library = generate_library()
        
        # Verify iconUrl uses local proxy endpoint with base game's title_id
        self.assertEqual(len(library), 1)
        dlc = library[0]
        self.assertEqual(dlc['iconUrl'], '/api/shop/icon/0100000000010000')
        
        # Verify other fields
        self.assertEqual(dlc['name'], 'Test DLC')
        self.assertEqual(dlc['title_id'], '0100000000010000')
        self.assertEqual(dlc['app_id'], '0100000000010001')


if __name__ == '__main__':
    unittest.main()
