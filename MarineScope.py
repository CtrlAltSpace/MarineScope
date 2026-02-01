# MarineScope.py - OPTIMIZED VERSION with FASTER SEARCH
import sys
import json
import os
import io
import hashlib
import re
import random
import base64
from typing import Optional, Dict, Any, List, Tuple
import time
from dataclasses import dataclass
import math
import concurrent.futures
from functools import lru_cache
from collections import OrderedDict

try:
    import requests
    from PIL import Image, ImageFile
    from PyQt6.QtCore import Qt, QThread, pyqtSignal, QSize, QTimer, QUrl
    from PyQt6.QtGui import (QPixmap, QImage, QFont, QPalette, QColor, QIcon, 
                            QDesktopServices, QFontDatabase, QPainter, QPen, QTransform, QTextOption,
                            QTextDocument)
    from PyQt6.QtWidgets import (
        QApplication, QMainWindow, QWidget, QHBoxLayout, QVBoxLayout,
        QLineEdit, QPushButton, QListWidget, QListWidgetItem, QLabel,
        QTextEdit, QFileDialog, QFormLayout, QSpinBox, QMessageBox, QDialog,
        QDialogButtonBox, QGroupBox, QProgressBar, QTabWidget, QFrame,
        QScrollArea, QGridLayout, QSizePolicy, QStackedWidget, QToolButton,
        QComboBox, QCheckBox, QSplitter, QProgressDialog, QSplashScreen
    )
    print(">>> DEBUG: All imports successful")
except ImportError as e:
    print(f">>> DEBUG: Import error: {e}")
    print("Please install required packages: pip install PyQt6 requests Pillow")
    sys.exit(1)

# Enable PIL to load truncated images
ImageFile.LOAD_TRUNCATED_IMAGES = True

# ==================== API ENDPOINTS ====================
USER_SPECIES_FILE = "user_species.json"

# WoRMS API settings - CORRECTED ENDPOINTS
WORMS_API_BASE = "https://www.marinespecies.org/rest"
WORMS_API_SEARCH = f"{WORMS_API_BASE}/AphiaRecordsByName"
WORMS_API_RECORD = f"{WORMS_API_BASE}/AphiaRecordByAphiaID"
WORMS_API_CLASSIFICATION = f"{WORMS_API_BASE}/AphiaClassificationByAphiaID"
WORMS_API_CHILDREN = f"{WORMS_API_BASE}/AphiaChildrenByAphiaID"
WORMS_API_DISTRIBUTION = f"{WORMS_API_BASE}/AphiaDistributionsByAphiaID"
WORMS_API_VERNACULARS = f"{WORMS_API_BASE}/AphiaVernacularsByAphiaID"
WORMS_API_VERNACULAR_SEARCH = f"{WORMS_API_BASE}/AphiaRecordsByVernacular"  # For common name search
WORMS_API_IMAGES = f"{WORMS_API_BASE}/AphiaImagesByAphiaID"  # Image endpoint

# OBIS API settings
OBIS_API_BASE = "https://api.obis.org"
OBIS_API_OCCURRENCES = f"{OBIS_API_BASE}/v3/occurrence"

# Wikipedia API
WIKI_API_ENDPOINT = "https://en.wikipedia.org/w/api.php"

# Style constants - LIGHT MODE
LIGHT_PRIMARY_COLOR = "#2c3e50"
LIGHT_SECONDARY_COLOR = "#3498db"
LIGHT_ACCENT_COLOR = "#1abc9c"
LIGHT_WARNING_COLOR = "#e74c3c"
LIGHT_SUCCESS_COLOR = "#27ae60"
LIGHT_LIGHT_BG = "#f8f9fa"
LIGHT_DARK_BG = "#ecf0f1"
LIGHT_BORDER_COLOR = "#bdc3c7"
LIGHT_TEXT_COLOR = "#2c3e50"
LIGHT_TEXT_SECONDARY = "#7f8c8d"

# DARK MODE colors
DARK_PRIMARY_COLOR = "#ecf0f1"
DARK_SECONDARY_COLOR = "#3498db"
DARK_ACCENT_COLOR = "#1abc9c"
DARK_WARNING_COLOR = "#e74c3c"
DARK_SUCCESS_COLOR = "#27ae60"
DARK_LIGHT_BG = "#2c3e50"
DARK_DARK_BG = "#2c3e50"
DARK_BORDER_COLOR = "#5d6d7e"
DARK_TEXT_COLOR = "#ecf0f1"
DARK_TEXT_SECONDARY = "#bdc3c7"

# Current theme (default: light)
PRIMARY_COLOR = LIGHT_PRIMARY_COLOR
SECONDARY_COLOR = LIGHT_SECONDARY_COLOR
ACCENT_COLOR = LIGHT_ACCENT_COLOR
WARNING_COLOR = LIGHT_WARNING_COLOR
SUCCESS_COLOR = LIGHT_SUCCESS_COLOR
LIGHT_BG = LIGHT_LIGHT_BG
DARK_BG = LIGHT_DARK_BG
BORDER_COLOR = LIGHT_BORDER_COLOR
TEXT_COLOR = LIGHT_TEXT_COLOR
TEXT_SECONDARY = LIGHT_TEXT_SECONDARY
IS_DARK_MODE = False

# Enhanced Cache for API responses with LRU and TTL
class APICache:
    def __init__(self, max_size=1000, ttl=3600):
        self.cache = OrderedDict()
        self.max_size = max_size
        self.ttl = ttl
    
    def get(self, key):
        if key in self.cache:
            data, timestamp = self.cache[key]
            if time.time() - timestamp < self.ttl:
                # Move to end (most recently used)
                self.cache.move_to_end(key)
                return data
            else:
                # Expired
                del self.cache[key]
        return None
    
    def set(self, key, value):
        if key in self.cache:
            self.cache.move_to_end(key)
        elif len(self.cache) >= self.max_size:
            # Remove oldest
            self.cache.popitem(last=False)
        self.cache[key] = (value, time.time())
    
    def clear(self):
        self.cache.clear()

API_CACHE = APICache(max_size=2000, ttl=3600)

# Pre-compiled regex patterns for faster string operations
SCIENTIFIC_NAME_PATTERN = re.compile(r'^[A-Z][a-z]+\s+[a-z]+$')
SCIENTIFIC_NAME_EXTRACT_PATTERNS = [
    re.compile(r'\b([A-Z][a-z]+)\s+([a-z]{2,})\b'),
    re.compile(r'\(([A-Z][a-z]+\s+[a-z]{2,})\)'),
    re.compile(r'\b(?:species|genus|family|order|class)\s+([A-Z][a-z]+\s+[a-z]{2,})\b'),
    re.compile(r'\b([A-Z])\.\s+([a-z]{2,})\b(?![a-z])'),
]
DEPTH_PATTERNS = [
    re.compile(r'depth[\s\w]{0,30}?(\d{1,5})\s*m', re.IGNORECASE),
    re.compile(r'(\d{1,5})\s*m[\s\w]{0,20}depth', re.IGNORECASE),
    re.compile(r'(\d{1,5})\s*-\s*(\d{1,5})\s*m', re.IGNORECASE),
    re.compile(r'(\d{1,5})\s*meter', re.IGNORECASE),
    re.compile(r'(\d{1,5})\s*to\s*(\d{1,5})\s*m', re.IGNORECASE),
]

# Common false positives for scientific names
COMMON_FALSE_POSITIVES = {
    'sharks are', 'modern sharks', 'some sources', 'the earliest',
    'jurassic around', 'sharks range', 'fish are', 'most fish',
    'many fish', 'the study', 'there are', 'the first',
    'age of', 'bony fish', 'fish have', 'commercial and',
    'turtles are', 'many turtles', 'sea turtles', 'turtles have',
    'some terrestrial', 'turtle habitats'
}

COMMON_WORDS = {
    'are', 'and', 'the', 'for', 'with', 'from', 'that', 'which',
    'have', 'has', 'had', 'can', 'may', 'might', 'will', 'would',
    'could', 'should', 'must', 'shall'
}

# Browsing state
BROWSE_OFFSET = 0
BROWSE_LIMIT_INITIAL = 20  # Initial species to load when browsing
BROWSE_LIMIT_INCREMENT = 5  # Additional species to load with "Browse More"

# ==================== STARTUP SCREEN ====================
class StartupScreen(QSplashScreen):
    """Startup splash screen"""
    def __init__(self):
        # Create a pixmap with the desired background color
        pixmap = QPixmap(400, 300)
        pixmap.fill(QColor("#fffef7"))
        
        super().__init__(pixmap)
        
        self.setWindowTitle("MarineScope")
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint)
        
        # Add layout for content
        layout = QVBoxLayout()
        layout.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
        # Add your image here
        image_label = QLabel()
        image_label.setStyleSheet("margin-top: 75px;")
        
        # Try to load the image from exact path
        try:
            # EXACT PATH TO YOUR IMAGE
            image_path = r"D:\Python codes\MarineScope\MarineScope_logo.png"
            
            if os.path.exists(image_path):
                pixmap = QPixmap(image_path)
                
                # Resize the image
                pixmap = pixmap.scaled(600, 600, 
                                    Qt.AspectRatioMode.KeepAspectRatio,
                                    Qt.TransformationMode.SmoothTransformation)
                
                image_label.setPixmap(pixmap)
                image_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
                print(f">>> DEBUG: Startup image loaded from: {image_path}")
            else:
                # Fallback text if image not found
                image_label.setText("🌊 MarineScope")
                image_label.setStyleSheet("font-size: 32px; color: #2c3e50; font-weight: bold;")
                print(f">>> DEBUG: Image not found at: {image_path}")
                
        except Exception as e:
            print(f">>> DEBUG: Error loading startup image: {e}")
            image_label.setText("🌊 MarineScope")
            image_label.setStyleSheet("font-size: 32px; color: #2c3e50; font-weight: bold;")
        
        layout.addWidget(image_label)
        
        # Add loading text
        self.loading_label = QLabel("Loading marine database...")
        self.loading_label.setStyleSheet(f"font-size: 14px; color: {TEXT_COLOR}; margin-top: 20px;")
        self.loading_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.loading_label)
        
        # Add progress bar
        self.progress_bar = QProgressBar()
        self.progress_bar.setRange(0, 100)
        self.progress_bar.setTextVisible(False)
        self.progress_bar.setStyleSheet(f"""
            QProgressBar {{
                border: 1px solid {LIGHT_BORDER_COLOR};
                border-radius: 4px;
                background: white;
                height: 8px;
                width: 500px;
            }}
            QProgressBar::chunk {{
                background: {LIGHT_SECONDARY_COLOR};
                border-radius: 4px;
            }}
        """)
        layout.addWidget(self.progress_bar, 0, Qt.AlignmentFlag.AlignCenter)
        
        # Set the layout directly on the QSplashScreen
        self.setLayout(layout)
        
        # Set background color
        self.setStyleSheet(f"background-color: #fffef7;")
    
    def update_progress(self, value: int, message: str = ""):
        """Update progress bar and message"""
        self.progress_bar.setValue(value)
        if message:
            self.loading_label.setText(message)
        QApplication.processEvents()

# ==================== OPTIMIZED DATA FUNCTIONS ====================
@lru_cache(maxsize=100)
def fetch_high_level_taxa_cached():
    """Fetch high-level marine taxa from WoRMS, focusing on traditional marine animals"""
    try:
        # Focus on traditional marine animals (fish, mammals, etc.)
        marine_animal_groups = [
            "Cetacea", "Actinopterygii", "Elasmobranchii", "Chondrichthyes",
            "Mammalia", "Pinnipedia", "Sirenia", "Cephalopoda"
        ]
        
        high_level_taxa = []
        seen_ids = set()
        
        for group in marine_animal_groups:
            params = {
                'scientificname': group,
                'marine_only': True,
                'like': False,
                'offset': 1,
                'limit': 5
            }
            
            data = api_request_with_cache(WORMS_API_SEARCH, params=params)
            if not data:
                continue
            
            items = data if isinstance(data, list) else [data]
            for item in items:
                aphia_id = item.get('AphiaID')
                rank = item.get('rank', '').lower()
                scientific = item.get('scientificname', '')
                is_marine = item.get('isMarine', False)
                
                # Focus on classes and orders of marine animals
                if (aphia_id and is_marine and rank in ['class', 'order', 'subclass'] and
                    aphia_id not in seen_ids):
                    
                    # Get common name if available
                    common_name = get_vernacular_name_cached(aphia_id)
                    display_name = common_name or scientific
                    
                    high_level_taxa.append({
                        "name": display_name,
                        "aphia_id": aphia_id,
                        "rank": rank.capitalize(),
                        "scientific": scientific
                    })
                    seen_ids.add(aphia_id)
                    
                    if len(high_level_taxa) >= 8:
                        break
            
            if len(high_level_taxa) >= 8:
                break
        
        # If we didn't get enough, add well-known marine animal groups
        if len(high_level_taxa) < 5:
            default_taxa = [
                {"name": "Whales & Dolphins", "aphia_id": 1837, "rank": "Order", "scientific": "Cetacea"},
                {"name": "Bony Fish", "aphia_id": 10194, "rank": "Class", "scientific": "Actinopterygii"},
                {"name": "Sharks & Rays", "aphia_id": 10215, "rank": "Class", "scientific": "Elasmobranchii"},
                {"name": "Marine Mammals", "aphia_id": 1836, "rank": "Infraorder", "scientific": "Cetacea"},
                {"name": "Squid & Octopus", "aphia_id": 123084, "rank": "Class", "scientific": "Cephalopoda"},
            ]
            
            for taxon in default_taxa:
                if taxon['aphia_id'] not in seen_ids:
                    high_level_taxa.append(taxon)
                    seen_ids.add(taxon['aphia_id'])
        
        return high_level_taxa[:8]
        
    except Exception as e:
        print(f">>> DEBUG: Error fetching high-level taxa: {e}")
        # Fallback to marine animal-focused taxa
        return [
            {"name": "Whales & Dolphins", "aphia_id": 1837, "rank": "Order", "scientific": "Cetacea"},
            {"name": "Bony Fish", "aphia_id": 10194, "rank": "Class", "scientific": "Actinopterygii"},
            {"name": "Sharks & Rays", "aphia_id": 10215, "rank": "Class", "scientific": "Elasmobranchii"},
            {"name": "Squid & Octopus", "aphia_id": 123084, "rank": "Class", "scientific": "Cephalopoda"},
            {"name": "Sea Turtles", "aphia_id": 1840, "rank": "Order", "scientific": "Testudines"},
        ]

@lru_cache(maxsize=500)
def get_vernacular_name_cached(aphia_id: int) -> Optional[str]:
    """Get vernacular name for a taxon with caching"""
    try:
        url = f"{WORMS_API_VERNACULARS}/{aphia_id}"
        data = api_request_with_cache(url)
        if data and isinstance(data, list):
            for v in data:
                if v.get('language', '').lower() == 'english':
                    return v.get('vernacular', '').strip()
        return None
    except:
        return None

# Initialize high-level taxa
HIGH_LEVEL_TAXA = []

# ==================== THEME MANAGEMENT ====================
def toggle_dark_mode():
    """Toggle between light and dark mode"""
    global IS_DARK_MODE, PRIMARY_COLOR, SECONDARY_COLOR, ACCENT_COLOR, WARNING_COLOR, SUCCESS_COLOR
    global LIGHT_BG, DARK_BG, BORDER_COLOR, TEXT_COLOR, TEXT_SECONDARY
    
    IS_DARK_MODE = not IS_DARK_MODE
    
    if IS_DARK_MODE:
        # Switch to dark mode colors
        PRIMARY_COLOR = DARK_PRIMARY_COLOR
        SECONDARY_COLOR = DARK_SECONDARY_COLOR
        ACCENT_COLOR = DARK_ACCENT_COLOR
        WARNING_COLOR = DARK_WARNING_COLOR
        SUCCESS_COLOR = DARK_SUCCESS_COLOR
        LIGHT_BG = DARK_LIGHT_BG
        DARK_BG = DARK_DARK_BG
        BORDER_COLOR = DARK_BORDER_COLOR
        TEXT_COLOR = DARK_TEXT_COLOR
        TEXT_SECONDARY = DARK_TEXT_SECONDARY
        print(">>> DEBUG: Switched to DARK mode")
    else:
        # Switch to light mode colors
        PRIMARY_COLOR = LIGHT_PRIMARY_COLOR
        SECONDARY_COLOR = LIGHT_SECONDARY_COLOR
        ACCENT_COLOR = LIGHT_ACCENT_COLOR
        WARNING_COLOR = LIGHT_WARNING_COLOR
        SUCCESS_COLOR = LIGHT_SUCCESS_COLOR
        LIGHT_BG = LIGHT_LIGHT_BG
        DARK_BG = LIGHT_DARK_BG
        BORDER_COLOR = LIGHT_BORDER_COLOR
        TEXT_COLOR = LIGHT_TEXT_COLOR
        TEXT_SECONDARY = LIGHT_TEXT_SECONDARY
        print(">>> DEBUG: Switched to LIGHT mode")

def get_theme_stylesheet():
    """Get the current theme stylesheet"""
    if IS_DARK_MODE:
        return f"""
            QMainWindow, QWidget {{
                background-color: {LIGHT_BG};
                color: {TEXT_COLOR};
            }}
            QGroupBox {{
                font-weight: bold;
                border: 2px solid {BORDER_COLOR};
                border-radius: 6px;
                margin-top: 10px;
                padding-top: 10px;
                margin: 2px;
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
                color: {TEXT_COLOR};
            }}
            QLineEdit, QTextEdit, QSpinBox {{
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 5px;
            }}
            QListWidget {{
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
            }}
            QListWidget::item {{
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
            }}
            QListWidget::item:selected {{
                background-color: {SECONDARY_COLOR}40;
                color: {TEXT_COLOR};
            }}
            QTabWidget::pane {{
                border: 2px solid {BORDER_COLOR};
                border-radius: 6px;
                background-color: {DARK_BG};
            }}
            QTabBar::tab {{
                background-color: {LIGHT_BG};
                color: {TEXT_COLOR};
                padding: 8px 12px;
                margin-right: 2px;
                border-top-left-radius: 4px;
                border-top-right-radius: 4px;
            }}
            QTabBar::tab:selected {{
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
                border-bottom: 2px solid {SECONDARY_COLOR};
            }}
            QFrame {{
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
            }}
            QLabel {{
                color: {TEXT_COLOR};
            }}
            QProgressBar {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                background-color: {DARK_BG};
                color: {TEXT_COLOR};
            }}
            QProgressBar::chunk {{
                background-color: {SECONDARY_COLOR};
                border-radius: 4px;
            }}
            QScrollBar:vertical {{
                background-color: {LIGHT_BG};
                border: none;
                width: 14px;
                margin: 0px;
            }}
            QScrollBar::handle:vertical {{
                background-color: {BORDER_COLOR};
                border-radius: 0px;
                min-height: 30px;
                margin: 0px;
            }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
                border: none;
                background: none;
                height: 0px;
            }}
        """
    else:
        return f"""
            QMainWindow, QWidget {{
                background-color: {LIGHT_BG};
                color: {TEXT_COLOR};
            }}
            QGroupBox {{
                font-weight: bold;
                border: 2px solid {BORDER_COLOR};
                border-radius: 6px;
                margin-top: 10px;
                padding-top: 10px;
                margin: 2px;
                background-color: white;
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
            }}
            QLineEdit, QTextEdit, QSpinBox {{
                background-color: white;
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 5px;
            }}
            QListWidget {{
                background-color: white;
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
            }}
            QTabWidget::pane {{
                border: 2px solid {BORDER_COLOR};
                border-radius: 6px;
                background-color: white;
            }}
            QTabBar::tab {{
                background-color: {LIGHT_BG};
                padding: 8px 12px;
                margin-right: 2px;
                border-top-left-radius: 4px;
                border-top-right-radius: 4px;
            }}
            QTabBar::tab:selected {{
                background-color: white;
                border-bottom: 2px solid {SECONDARY_COLOR};
            }}
        """

# ==================== OPTIMIZED CORE FUNCTIONS ====================
def load_user_species() -> List[Dict[str, Any]]:
    """Load user-added species from JSON file"""
    try:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        user_species_path = os.path.join(script_dir, USER_SPECIES_FILE)
        with open(user_species_path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        print(f">>> DEBUG: Error loading user species: {e}")
        return []

def save_user_species(species_list: List[Dict[str, Any]]):
    """Save user species to JSON file"""
    try:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        user_species_path = os.path.join(script_dir, USER_SPECIES_FILE)
        with open(user_species_path, "w", encoding="utf-8") as f:
            json.dump(species_list, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print(f">>> DEBUG: Error saving user species: {e}")

def api_request_with_cache(url: str, params: Dict = None, cache_key: str = None, retries: int = 2) -> Optional[Dict]:  # Reduced retries
    """Make API request with caching and proper error handling"""
    if cache_key is None:
        cache_key = url + str(params)
    
    # Check cache
    cached_data = API_CACHE.get(cache_key)
    if cached_data is not None:
        return cached_data
    
    for attempt in range(retries + 1):
        try:
            headers = {
                'User-Agent': 'MarineScopeApp/1.0 (https://github.com/marinescope)',
                'Accept': 'application/json'
            }
            
            if 'marinespecies.org' in url:
                timeout = 10  # Reduced from 15
            elif 'api.obis.org' in url:
                timeout = 15  # Reduced from 20
            else:
                timeout = 8   # Reduced from 10
            
            # Clean API call logging - only log first time
            if attempt == 0:
                if 'marinespecies.org' in url:
                    if 'AphiaRecordsByName' in url:
                        if '/AphiaRecordsByName/' in url:
                            query_part = url.split('/AphiaRecordsByName/')[1].split('?')[0]
                            try:
                                query_name = requests.utils.unquote(query_part)
                                print(f">>> WoRMS SEARCH: {query_name}")
                            except:
                                print(f">>> WoRMS SEARCH: Unknown")
                        else:
                            print(f">>> WoRMS SEARCH: {params.get('scientificname', 'No name') if params else 'No params'}")
                    elif 'AphiaRecordByAphiaID' in url:
                        print(f">>> WoRMS LOOKUP: ID={url.split('/')[-1]}")
            
            response = requests.get(url, headers=headers, params=params, timeout=timeout)
            
            # Handle 204 No Content response
            if response.status_code == 204:
                print(f">>> DEBUG: API returned 204 No Content for {url}")
                API_CACHE.set(cache_key, None)
                return None
            
            if response.status_code == 404:
                print(f">>> DEBUG: API returned 404.")
                API_CACHE.set(cache_key, None)
                return None
            
            if response.status_code >= 400 and response.status_code != 204:
                if response.status_code == 429 and attempt < retries:
                    wait_time = 2 ** (attempt + 1)
                    time.sleep(wait_time)
                    continue
                API_CACHE.set(cache_key, None)
                return None
            
            if response.status_code == 204 or not response.content:
                API_CACHE.set(cache_key, None)
                return None
            
            response.raise_for_status()
            
            try:
                data = response.json()
                API_CACHE.set(cache_key, data)
                return data
            except json.JSONDecodeError as e:
                print(f">>> DEBUG: JSON decode error: {e}")
                API_CACHE.set(cache_key, None)
                return None
            
        except requests.exceptions.Timeout:
            if attempt < retries:
                time.sleep(0.5)  # Reduced
                continue
            API_CACHE.set(cache_key, None)
            return None
        except requests.exceptions.HTTPError as e:
            if e.response.status_code == 429 and attempt < retries:
                wait_time = 2 ** (attempt + 1)
                time.sleep(wait_time)
                continue
            API_CACHE.set(cache_key, None)
            return None
        except Exception as e:
            print(f">>> DEBUG: Request error: {e}")
            if attempt < retries:
                time.sleep(0.5)
                continue
            API_CACHE.set(cache_key, None)
            return None
    
    API_CACHE.set(cache_key, None)
    return None

def fetch_worms_children_parallel(aphia_ids: List[int]) -> Dict[int, List[Dict[str, Any]]]:
    """Fetch children taxa from WoRMS in parallel"""
    results = {}
    
    def fetch_single(aphia_id):
        try:
            url = f"{WORMS_API_CHILDREN}/{aphia_id}"
            cache_key = f"worms_children_{aphia_id}"
            
            data = api_request_with_cache(url, cache_key=cache_key)
            if not data:
                return aphia_id, []
            
            if isinstance(data, list):
                return aphia_id, data
            elif isinstance(data, dict):
                return aphia_id, [data]
            else:
                return aphia_id, []
        except Exception as e:
            print(f"Error fetching children for AphiaID {aphia_id}: {e}")
            return aphia_id, []
    
    # Use thread pool for parallel requests
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
        futures = {executor.submit(fetch_single, aphia_id): aphia_id for aphia_id in aphia_ids}
        for future in concurrent.futures.as_completed(futures):
            aphia_id, data = future.result()
            results[aphia_id] = data
    
    return results

def test_worms_api():
    """Test the WoRMS API directly - optimized"""
    test_queries = ["Orcinus orca", "137065", "Delphinus delphis"]
    
    for query in test_queries:
        print(f">>> Testing WoRMS API: '{query}'")
        
        if query.isdigit():
            url = f"{WORMS_API_RECORD}/{query}"
            response = requests.get(url, timeout=8)  # Reduced timeout
            if response.status_code == 200:
                try:
                    data = response.json()
                    print(f">>> ✓ Found: {data.get('scientificname', 'Unknown')}")
                except:
                    print(f">>> ✗ Invalid response")
            continue
        
        # Test with optimized parameter format
        params = {'scientificname': query, 'offset': 1, 'limit': 3}
        response = requests.get(WORMS_API_SEARCH, params=params, timeout=8)
        
        if response.status_code == 200:
            try:
                data = response.json()
                count = len(data) if isinstance(data, list) else 1
                print(f">>> ✓ Found {count} results")
            except:
                print(f">>> ✗ Invalid JSON")
        else:
            print(f">>> ✗ HTTP {response.status_code}")

def is_scientific_name(query: str) -> bool:
    """Check if the query looks like a scientific name (Genus species) - optimized"""
    return bool(SCIENTIFIC_NAME_PATTERN.match(query.strip()))

def search_worms_species_robust(query: str) -> List[Dict[str, Any]]:
    """Robust search for species in WoRMS database - optimized"""
    results = []
    query_lower = query.lower().strip()
    
    print(f">>> DEBUG: Searching WoRMS for: '{query}'")
    
    # Encode the query for URL
    encoded_query = requests.utils.quote(query)
    
    # First try exact match
    exact_url = f"{WORMS_API_BASE}/AphiaRecordsByName/{encoded_query}?marine_only=true&like=false&offset=1&limit=10"  # Reduced limit
    data = api_request_with_cache(exact_url)
    
    if data and isinstance(data, list):
        for item in data:
            try:
                status = item.get('status', '').lower()
                aphia_id = item.get('AphiaID')
                
                if not aphia_id or status != 'accepted':
                    continue
                
                sci_name = item.get('scientificname', '').lower().strip()
                
                if sci_name == query_lower:
                    print(f">>> DEBUG: Found exact match: {sci_name}")
                    species_data = get_complete_species_data(aphia_id, query)
                    if species_data:
                        results.append(species_data)
                        return results
            except Exception as e:
                continue
    
    # If no exact match, try fuzzy search
    fuzzy_url = f"{WORMS_API_BASE}/AphiaRecordsByName/{encoded_query}?marine_only=true&like=true&offset=1&limit=15"  # Reduced limit
    data = api_request_with_cache(fuzzy_url)
    
    if data and isinstance(data, list):
        for item in data:
            try:
                status = item.get('status', '').lower()
                aphia_id = item.get('AphiaID')
                
                if not aphia_id or status != 'accepted':
                    continue
                
                sci_name = item.get('scientificname', '').lower().strip()
                
                # Check for close match
                is_close_match = (query_lower in sci_name) or (sci_name in query_lower)
                
                if is_close_match:
                    print(f">>> DEBUG: Found close match: {sci_name}")
                    species_data = get_complete_species_data(aphia_id, query)
                    if species_data:
                        if not any(r.get('aphia_id') == aphia_id for r in results):
                            results.append(species_data)
            except Exception as e:
                continue
    
    print(f">>> DEBUG: Found {len(results)} results")
    return results[:8]  # Reduced from 10

def extract_scientific_names_from_text_fast(text: str) -> List[str]:
    """Extract potential scientific names from Wikipedia text - optimized"""
    if not text:
        return []
    
    scientific_names = []
    
    # Use pre-compiled patterns
    for pattern in SCIENTIFIC_NAME_EXTRACT_PATTERNS:
        matches = pattern.findall(text)
        for match in matches:
            if isinstance(match, tuple):
                if len(match) == 2:
                    # Skip if it's clearly not a scientific name
                    if match[0].lower() in ['sharks', 'turtles', 'fish', 'whales', 'dolphins', 
                                           'modern', 'some', 'the', 'their', 'these', 'those',
                                           'many', 'most', 'all', 'few', 'several']:
                        continue
                    
                    # Skip if the second part looks like a common English word
                    if match[1].lower() in COMMON_WORDS:
                        continue
                    
                    sci_name = f"{match[0]} {match[1]}"
                    # Additional validation: genus should be capitalized, species lowercase
                    if match[0][0].isupper() and match[1][0].islower():
                        if sci_name not in scientific_names:
                            scientific_names.append(sci_name)
            elif isinstance(match, str):
                if match and match[0].isupper() and ' ' in match:
                    genus, species = match.split(' ', 1)
                    if genus[0].isupper() and species and species[0].islower():
                        if match not in scientific_names:
                            scientific_names.append(match)
    
    # Filter out common false positives using set for O(1) lookup
    filtered_names = []
    for name in scientific_names:
        # Skip names that are clearly not scientific names
        if name.lower() in COMMON_FALSE_POSITIVES:
            continue
        
        parts = name.split()
        if len(parts) == 2:
            genus, species = parts
            
            # More validation
            if (genus[0].isupper() and len(genus) > 1 and 
                species[0].islower() and len(species) > 1 and
                genus.lower() not in ['sharks', 'fish', 'turtles', 'whales', 'dolphins'] and
                species not in COMMON_WORDS):
                filtered_names.append(name)
    
    # Remove duplicates while preserving order
    seen = set()
    unique_names = []
    for name in filtered_names:
        if name not in seen:
            seen.add(name)
            unique_names.append(name)
    
    return unique_names

def wikipedia_mediated_search_fast(common_name: str) -> List[Dict[str, Any]]:
    """Use Wikipedia to find scientific name, then search WoRMS - optimized"""
    try:
        print(f">>> DEBUG: Starting Wikipedia-mediated search for '{common_name}'")
        
        # Get Wikipedia data
        wiki_data = get_wikipedia_data_fast(common_name)
        if not wiki_data or not wiki_data.get('description'):
            print(f">>> DEBUG: No Wikipedia data found")
            return []
        
        wiki_extract = wiki_data['description']
        
        # Extract scientific names from Wikipedia text
        scientific_names = extract_scientific_names_from_text_fast(wiki_extract)
        
        # Try each scientific name
        for sci_name in scientific_names[:3]:  # Limit to 3
            print(f">>> DEBUG: Trying scientific name from Wikipedia: '{sci_name}'")
            results = search_worms_species_robust(sci_name)
            if results:
                print(f">>> DEBUG: Found {len(results)} results with '{sci_name}'")
                return results
        
        print(f">>> DEBUG: Wikipedia-mediated search found no results")
        return []
        
    except Exception as e:
        print(f">>> DEBUG: Error in Wikipedia-mediated search: {e}")
        return []

def search_by_common_name_fast(common_name: str) -> List[Dict[str, Any]]:
    """Enhanced search for species by common/vernacular name - optimized"""
    try:
        print(f">>> DEBUG: Enhanced search for common name: '{common_name}'")
        
        # Try the WoRMS vernacular API first
        encoded_name = requests.utils.quote(common_name)
        url = f"{WORMS_API_VERNACULAR_SEARCH}/{encoded_name}"
        
        data = api_request_with_cache(url)
        
        # Handle 204 No Content response
        if data is None:
            print(f">>> DEBUG: WoRMS returned 204 for '{common_name}', trying Wikipedia-mediated search...")
            return wikipedia_mediated_search_fast(common_name)
        
        if not data or not isinstance(data, list):
            print(f">>> DEBUG: No vernacular results found for '{common_name}'")
            return wikipedia_mediated_search_fast(common_name)
        
        # Process the results
        results = []
        seen_ids = set()
        
        for item in data[:8]:  # Limit processing
            try:
                aphia_id = item.get('AphiaID')
                
                if not aphia_id or aphia_id in seen_ids:
                    continue
                
                record_data = api_request_with_cache(f"{WORMS_API_RECORD}/{aphia_id}")
                if not record_data:
                    continue
                
                status = record_data.get('status', '').lower()
                is_marine = record_data.get('isMarine', False)
                
                if status != 'accepted' or not is_marine:
                    continue
                
                species_data = get_complete_species_data(aphia_id, common_name)
                if species_data:
                    results.append(species_data)
                    seen_ids.add(aphia_id)
                    
                    if len(results) >= 5:  # Reduced
                        break
                        
            except Exception as e:
                continue
        
        if results:
            print(f">>> DEBUG: Found {len(results)} results by common name")
            return results
        else:
            print(f">>> DEBUG: No valid results from WoRMS, trying Wikipedia...")
            return wikipedia_mediated_search_fast(common_name)
        
    except Exception as e:
        print(f">>> DEBUG: Error searching by common name: {e}")
        return wikipedia_mediated_search_fast(common_name)

def fuzzy_search_common_name_fast(query: str) -> List[Dict[str, Any]]:
    """Enhanced fuzzy search using Wikipedia to find scientific names - optimized"""
    try:
        print(f">>> DEBUG: Enhanced fuzzy searching for: '{query}'")
        
        # Get Wikipedia data
        wiki_data = get_wikipedia_data_fast(query)
        if not wiki_data:
            print(f">>> DEBUG: No Wikipedia data found for '{query}'")
            return []
        
        wiki_title = wiki_data.get('title', '')
        wiki_extract = wiki_data.get('description', '')
        
        # Extract potential scientific names from Wikipedia text
        scientific_names = extract_scientific_names_from_text_fast(wiki_extract)
        
        # Also try the Wikipedia title if it looks like a scientific name
        if is_scientific_name(wiki_title):
            scientific_names.append(wiki_title)
        
        # Try each potential scientific name
        for sci_name in scientific_names[:3]:  # Limit to 3
            print(f">>> DEBUG: Trying scientific name: '{sci_name}'")
            results = search_worms_species_robust(sci_name)
            if results:
                print(f">>> DEBUG: Found {len(results)} results with scientific name '{sci_name}'")
                return results
        
        # If no scientific names found, try alternative approaches
        results = search_worms_species_robust(wiki_title)
        if results:
            return results
        
        print(f">>> DEBUG: No results found through enhanced fuzzy search")
        return []
        
    except Exception as e:
        print(f">>> DEBUG: Error in enhanced fuzzy search: {e}")
        return []

def search_worms_species_fast(query: str) -> List[Dict[str, Any]]:
    """Search for species in WoRMS database, handling both scientific and common names - optimized"""
    try:
        clean_query = query.strip()
        if not clean_query or len(clean_query) < 2:
            return []
        
        print(f">>> DEBUG: Enhanced search for: '{clean_query}'")
        
        # Check if query is an AphiaID (numeric)
        if clean_query.isdigit():
            aphia_id = int(clean_query)
            species_data = get_complete_species_data(aphia_id, "")
            if species_data:
                return [species_data]
            else:
                return []
        
        # Check if query is a scientific name
        if is_scientific_name(clean_query):
            print(f">>> DEBUG: Query looks like a scientific name, searching directly")
            return search_worms_species_robust(clean_query)
        
        # First, try exact scientific name search
        results = search_worms_species_robust(clean_query)
        
        # If no results, try enhanced common name search
        if not results:
            results = search_by_common_name_fast(clean_query)
        
        # If still no results, try Wikipedia-mediated fuzzy search
        if not results:
            results = fuzzy_search_common_name_fast(clean_query)
        
        print(f">>> DEBUG: Final result: {len(results)} species found")
        return results[:10]  # Reduced from 15
        
    except Exception as e:
        print(f">>> DEBUG: Error searching WoRMS for '{query}': {e}")
        return []

def get_worms_images_fast(aphia_id: int) -> List[str]:
    """Get image URLs from WoRMS for a species - optimized"""
    try:
        # First try the AphiaImagesByAphiaID endpoint
        images_url = f"{WORMS_API_BASE}/AphiaImagesByAphiaID/{aphia_id}"
        
        data = api_request_with_cache(images_url, cache_key=f"worms_images_{aphia_id}")
        
        image_urls = []
        
        if data and isinstance(data, list):
            for image_data in data[:3]:  # Limit processing
                if isinstance(image_data, dict):
                    # Try different possible image URL fields
                    url_fields = ['url', 'thumbnail_url', 'image_url']
                    
                    # Check direct URL fields
                    for field in url_fields:
                        if field in image_data and image_data[field]:
                            url = image_data[field]
                            if isinstance(url, str) and url.startswith(('http://', 'https://')):
                                # Ensure HTTPS
                                if url.startswith('http://'):
                                    url = url.replace('http://', 'https://')
                                if url not in image_urls:
                                    image_urls.append(url)
                                    break
        
        # If no images found in AphiaImages, try the main record
        if not image_urls:
            record_url = f"{WORMS_API_RECORD}/{aphia_id}"
            record_data = api_request_with_cache(record_url, cache_key=f"worms_record_{aphia_id}")
            
            if record_data and 'picture_url' in record_data and record_data['picture_url']:
                url = record_data['picture_url']
                if url.startswith(('http://', 'https://')):
                    url = url.replace('http://', 'https://') if url.startswith('http://') else url
                    image_urls.append(url)
        
        return image_urls[:3]  # Return up to 3 images
        
    except Exception as e:
        print(f">>> DEBUG: Error getting WoRMS images for AphiaID {aphia_id}: {e}")
        return []

def get_worms_image_fast(aphia_id: int) -> Optional[str]:
    """Get the best image URL from WoRMS for a species - optimized"""
    try:
        images = get_worms_images_fast(aphia_id)
        if images:
            return images[0]
        return None
    except Exception as e:
        return None

def get_wikipedia_data_fast(search_term: str) -> Dict[str, Any]:
    """Get Wikipedia data for images and descriptions - optimized"""
    try:
        # Clean the search term
        search_term = search_term.strip()
        
        # First try the exact search
        params_intro = {
            'action': 'query',
            'titles': search_term,
            'prop': 'extracts|pageimages',
            'exintro': True,
            'explaintext': True,
            'pithumbsize': 300,  # Smaller thumbnail
            'pilimit': 3,  # Reduced
            'format': 'json',
            'utf8': True
        }
        
        data = api_request_with_cache(WIKI_API_ENDPOINT, params=params_intro)
        if not data:
            return {}
        
        pages = data.get('query', {}).get('pages', {})
        
        for pid, page in pages.items():
            if pid == '-1':  # Page not found
                continue
            
            extract = page.get('extract', '')
            thumbnail = page.get('thumbnail', {})
            page_title = page.get('title', '')
            
            # Check if extract is meaningful
            if extract and len(extract.strip()) > 30:  # Reduced threshold
                thumb_url = None
                
                # Try to get thumbnail
                if thumbnail and thumbnail.get('source'):
                    thumb_url = thumbnail.get('source')
                
                is_common_name = not SCIENTIFIC_NAME_PATTERN.match(page_title)
                
                return {
                    'description': extract.strip(),
                    'thumb_url': thumb_url,
                    'title': page_title,
                    'is_common_name': is_common_name,
                    'url': page.get('fullurl', '')
                }
        
        return {}
        
    except Exception as e:
        return {}

def get_complete_species_data_parallel(aphia_id: int, search_term: str = None) -> Optional[Dict[str, Any]]:
    """Get complete species data from WoRMS, OBIS, and Wikipedia - optimized with parallel requests"""
    try:
        if not aphia_id:
            return None
            
        # Get basic record
        record_data = api_request_with_cache(f"{WORMS_API_RECORD}/{aphia_id}")
        if not record_data:
            return None
        
        if not record_data.get('scientificname') and not record_data.get('valid_name'):
            return None
        
        # Get additional data in parallel where possible
        scientific_name = record_data.get('scientificname')
        
        # Prepare data collection
        results = {}
        
        def fetch_classification():
            return api_request_with_cache(f"{WORMS_API_CLASSIFICATION}/{aphia_id}")
        
        def fetch_distribution():
            return api_request_with_cache(f"{WORMS_API_DISTRIBUTION}/{aphia_id}")
        
        def fetch_obis():
            if scientific_name:
                return get_obis_data_fast(scientific_name)
            return None
        
        def fetch_wiki():
            search_terms = []
            if search_term:
                search_terms.append(search_term)
            if record_data.get('valid_name'):
                search_terms.append(record_data.get('valid_name'))
            if scientific_name:
                search_terms.append(scientific_name)
            
            for term in search_terms:
                if term and term != "null":
                    wiki_data = get_wikipedia_data_fast(term)
                    if wiki_data and wiki_data.get('description'):
                        return wiki_data
            return {}
        
        # Execute parallel requests
        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            futures = {
                'classification': executor.submit(fetch_classification),
                'distribution': executor.submit(fetch_distribution),
                'obis': executor.submit(fetch_obis),
                'wiki': executor.submit(fetch_wiki)
            }
            
            for key, future in futures.items():
                try:
                    results[key] = future.result(timeout=10)
                except:
                    results[key] = None
        
        classification_data = results['classification']
        distribution_data = results['distribution']
        obis_data = results['obis']
        wiki_data = results['wiki'] or {}
        
        # Try to get image from WoRMS
        worms_image_url = get_worms_image_fast(aphia_id)
        
        # Extract all information
        habitat_info = extract_habitat_info_fast(record_data, classification_data, obis_data)
        depth_info = extract_depth_from_obis_fast(obis_data, record_data)
        distribution = extract_distribution_fast(distribution_data, obis_data, record_data)
        taxonomy = extract_taxonomy_fast(classification_data)
        ocean_basins = extract_ocean_basins_fast(obis_data)
        occurrence_stats = extract_occurrence_stats_fast(obis_data)
        
        # Extract common name
        common_name = extract_common_name_fast(record_data, wiki_data, search_term, scientific_name)
        
        # Prepare description
        description = create_description_fast(
            common_name, scientific_name, habitat_info, 
            distribution, depth_info, record_data, wiki_data
        )
        
        # Determine image source
        thumb_url, image_source = determine_image_source_fast(worms_image_url, wiki_data, scientific_name)
        
        print(f">>> ✓ Assembled: {scientific_name}")
        
        return {
            'title': record_data.get('valid_name') or record_data.get('scientificname', 'Unknown'),
            'common_name': common_name,
            'latin_name': scientific_name,
            'aphia_id': aphia_id,
            'habitat': habitat_info,
            'depth_info': depth_info,
            'distribution': distribution,
            'ocean_basins': ocean_basins,
            'occurrence_stats': occurrence_stats,
            'extract': description,
            'thumb_url': thumb_url,
            'image_source': image_source,
            'wiki_url': wiki_data.get('url'),
            'taxonomy': taxonomy,
            'source': 'worms_obis',
            'is_marine': record_data.get('isMarine', False),
            'is_brackish': record_data.get('isBrackish', False),
            'is_freshwater': record_data.get('isFreshwater', False),
            'is_terrestrial': record_data.get('isTerrestrial', False)
        }
    except Exception as e:
        print(f"Error getting complete species data for ID {aphia_id}: {e}")
        return None

def extract_common_name_fast(record_data, wiki_data, search_term, scientific_name):
    """Extract common name efficiently"""
    common_name = ""
    
    # Try from record data
    if record_data.get('vernaculars'):
        vernaculars = record_data.get('vernaculars')
        if isinstance(vernaculars, list) and len(vernaculars) > 0:
            for v in vernaculars[:2]:  # Check first 2 only
                if isinstance(v, dict) and 'vernacular' in v:
                    name = v.get('vernacular', '').strip()
                    if name:
                        lang = v.get('language', '').lower()
                        if lang == 'english':
                            return name
                        elif not common_name:
                            common_name = name
    
    if not common_name and record_data.get('valid_vernacular'):
        return record_data.get('valid_vernacular', '').strip()
    
    if not common_name and wiki_data and wiki_data.get('title'):
        wiki_title = wiki_data['title']
        if not SCIENTIFIC_NAME_PATTERN.match(wiki_title):
            return wiki_title
    
    if not common_name and search_term and search_term != "null" and not SCIENTIFIC_NAME_PATTERN.match(search_term):
        return search_term
    
    return common_name or scientific_name

def create_description_fast(common_name, scientific_name, habitat_info, distribution, depth_info, record_data, wiki_data):
    """Create description efficiently"""
    # Try Wikipedia first
    if wiki_data and wiki_data.get('description') and len(wiki_data.get('description', '').strip()) > 30:
        return wiki_data.get('description')
    
    # Create descriptive summary
    description_parts = []
    
    if common_name and common_name != scientific_name:
        description_parts.append(f"The {common_name} ({scientific_name})")
    else:
        description_parts.append(f"The marine species {scientific_name}")
    
    if habitat_info:
        habitat_simple = habitat_info.split('(')[0].strip() if '(' in habitat_info else habitat_info
        description_parts.append(f"is a {habitat_simple.lower()} species.")
    else:
        description_parts.append("is a marine species.")
    
    if distribution and len(distribution) > 0:
        dist_text = ', '.join(distribution[:2])  # Reduced
        description_parts.append(f"It is found in {dist_text}.")
    
    if depth_info:
        avg_depth = depth_info.get('avg_depth', 0)
        if avg_depth < 200:
            depth_zone = "shallow coastal waters"
        elif avg_depth < 1000:
            depth_zone = "moderate depths"
        else:
            depth_zone = "deep ocean waters"
        description_parts.append(f"This species inhabits {depth_zone}.")
    
    return ' '.join(description_parts)

def determine_image_source_fast(worms_image_url, wiki_data, scientific_name):
    """Determine image source efficiently"""
    thumb_url = None
    image_source = None
    
    if worms_image_url:
        thumb_url = worms_image_url
        image_source = "WoRMS"
    elif wiki_data and wiki_data.get('thumb_url'):
        thumb_url = wiki_data.get('thumb_url')
        image_source = "Wikipedia"
    
    return thumb_url, image_source

def get_complete_species_data(aphia_id: int, search_term: str = None) -> Optional[Dict[str, Any]]:
    """Wrapper for backward compatibility"""
    return get_complete_species_data_parallel(aphia_id, search_term)

def get_obis_data_fast(scientific_name: str) -> Optional[Dict[str, Any]]:
    """Get depth and occurrence data from OBIS v3 - optimized"""
    try:
        occurrence_params = {
            'scientificname': scientific_name,
            'limit': 50,  # Reduced from 100
            'offset': 0
        }
        
        occurrences_data = api_request_with_cache(
            OBIS_API_OCCURRENCES, 
            params=occurrence_params,
            cache_key=f"obis_{scientific_name}"
        )
        
        if not occurrences_data:
            return None
        
        return {
            'occurrences': occurrences_data,
            'scientific_name': scientific_name
        }
    except Exception as e:
        return None

def extract_habitat_info_fast(record_data: Dict, classification_data: Dict, obis_data: Dict = None) -> str:
    """Extract habitat information - optimized"""
    habitat = "Marine"
    
    if record_data.get('isMarine'):
        habitat = "Marine"
        if record_data.get('isBrackish'):
            habitat += "/Brackish"
    
    environment = record_data.get('environment', '').lower()
    habitat_types = []
    
    # Predefined habitat mappings
    habitat_keywords = {
        'benthic': "Benthic",
        'pelagic': "Pelagic",
        'demersal': "Demersal",
        'reef': "Coral Reef",
        'coral': "Coral Reef",
        'intertidal': "Intertidal",
        'subtidal': "Subtidal"
    }
    
    for key, value in habitat_keywords.items():
        if key in environment:
            habitat_types.append(value)
    
    if obis_data and obis_data.get('occurrences'):
        depth_info = extract_depth_from_obis_fast(obis_data, record_data)
        if depth_info and 'avg_depth' in depth_info:
            avg_depth = depth_info['avg_depth']
            if avg_depth < 200:
                habitat_types.append("Epipelagic")
            elif avg_depth < 1000:
                habitat_types.append("Mesopelagic")
            else:
                habitat_types.append("Deep Sea")
    
    if habitat_types:
        habitat = f"{habitat} ({', '.join(habitat_types[:3])})"  # Limit to 3
    
    return habitat

def extract_depth_from_obis_fast(obis_data: Dict, worms_record: Dict) -> Optional[Dict[str, Any]]:
    """Extract depth information from OBIS v3 data - optimized"""
    depth_info = {}
    
    if obis_data and isinstance(obis_data, dict) and 'occurrences' in obis_data:
        occurrences = obis_data['occurrences']
        if isinstance(occurrences, dict):
            results = occurrences.get('results', [])
        else:
            results = []
        
        depths = []
        for occurrence in results[:20]:  # Limit processing
            depth = occurrence.get('depth')
            if depth is not None:
                try:
                    depths.append(float(depth))
                except:
                    pass
        
        if depths:
            depth_info['min_depth'] = min(depths)
            depth_info['max_depth'] = max(depths)
            depth_info['avg_depth'] = sum(depths) / len(depths)
            depth_info['record_count'] = len(depths)
            depth_info['source'] = 'OBIS v3'
            return depth_info
    
    # Try to extract from environment text using pre-compiled patterns
    environment = worms_record.get('environment', '')
    
    for pattern in DEPTH_PATTERNS:
        matches = pattern.findall(environment)
        if matches:
            try:
                if isinstance(matches[0], tuple):
                    nums = [int(m.replace(',', '').strip()) for m in matches[0] if m]
                    if nums:
                        depth_info['min_depth'] = min(nums)
                        depth_info['max_depth'] = max(nums)
                        depth_info['avg_depth'] = sum(nums) / len(nums)
                else:
                    depth_str = matches[0]
                    depth = int(depth_str.replace(',', '').strip())
                    depth_info['min_depth'] = depth
                    depth_info['max_depth'] = depth
                    depth_info['avg_depth'] = depth
                
                depth_info['record_count'] = 1
                depth_info['source'] = 'WoRMS'
                return depth_info
            except:
                continue
    
    return None

def extract_distribution_fast(distribution_data: Dict, obis_data: Dict, worms_record: Dict) -> List[str]:
    """Extract distribution information from multiple sources - optimized"""
    distribution = set()
    
    # First try WoRMS distribution data
    if distribution_data and isinstance(distribution_data, list):
        for dist in distribution_data[:5]:  # Limit
            locality = dist.get('locality')
            if locality:
                distribution.add(locality)
    
    # Then try OBIS data
    if obis_data and isinstance(obis_data, dict) and 'occurrences' in obis_data:
        occurrences = obis_data['occurrences']
        if isinstance(occurrences, dict):
            results = occurrences.get('results', [])
        else:
            results = []
        
        for occurrence in results[:5]:  # Limit
            for field in ['locality', 'waterBody', 'country']:
                value = occurrence.get(field)
                if value:
                    distribution.add(str(value))
                    break
    
    # Finally try WoRMS record data
    if not distribution and worms_record.get('distribution'):
        dist_text = worms_record.get('distribution')
        # Take first part before any separator
        for sep in [';', ',', '|']:
            if sep in dist_text:
                first_part = dist_text.split(sep)[0].strip()
                if first_part:
                    distribution.add(first_part)
                    break
        
        if not distribution and dist_text.strip():
            distribution.add(dist_text.strip())
    
    return list(distribution)[:4] if distribution else ["Global distribution"]  # Reduced

def extract_ocean_basins_fast(obis_data: Dict) -> List[str]:
    """Extract ocean basins from OBIS v3 data - optimized"""
    basins = set()
    
    if obis_data and isinstance(obis_data, dict) and 'occurrences' in obis_data:
        occurrences = obis_data['occurrences']
        if isinstance(occurrences, dict):
            results = occurrences.get('results', [])
        else:
            results = []
        
        for occurrence in results[:20]:  # Limit
            lat = occurrence.get('decimalLatitude')
            lon = occurrence.get('decimalLongitude')
            
            if lat is not None and lon is not None:
                if lon < -30:
                    if lat > 0:
                        basins.add("North Atlantic")
                    else:
                        basins.add("South Atlantic")
                elif -30 <= lon <= 30:
                    basins.add("Tropical Atlantic")
                elif lon > 100 and lon < 180:
                    if lat > 0:
                        basins.add("North Pacific")
                    else:
                        basins.add("South Pacific")
                elif lon < -100:
                    basins.add("Eastern Pacific")
                elif 30 < lon < 100:
                    basins.add("Indian Ocean")
    
    return list(basins)[:3] if basins else ["Multiple ocean basins"]  # Reduced

def extract_occurrence_stats_fast(obis_data: Dict) -> Dict[str, Any]:
    """Extract occurrence statistics - optimized"""
    stats = {
        'total_records': 0,
        'has_depth_data': False,
        'has_coordinates': False,
        'year_range': None
    }
    
    if obis_data and isinstance(obis_data, dict) and 'occurrences' in obis_data:
        occurrences = obis_data['occurrences']
        if isinstance(occurrences, dict):
            stats['total_records'] = occurrences.get('total', 0)
            
            results = occurrences.get('results', [])
            if results:
                years = []
                
                for occurrence in results[:10]:  # Limit
                    if occurrence.get('depth') is not None:
                        stats['has_depth_data'] = True
                    
                    if occurrence.get('decimalLatitude') is not None and occurrence.get('decimalLongitude') is not None:
                        stats['has_coordinates'] = True
                    
                    year = occurrence.get('year')
                    if year:
                        try:
                            years.append(int(year))
                        except:
                            pass
                
                if years:
                    stats['year_range'] = f"{min(years)}-{max(years)}"
    
    return stats

def extract_taxonomy_fast(classification_data: Dict) -> Dict[str, str]:
    """Extract taxonomy from classification data - optimized"""
    taxonomy = {}
    
    if not classification_data:
        return taxonomy
    
    def extract_from_node(node):
        if isinstance(node, dict):
            rank = node.get('rank', '').lower()
            name = node.get('scientificname', '')
            if rank and name and rank not in taxonomy:
                taxonomy[rank] = name
            
            child = node.get('child', {})
            if child:
                extract_from_node(child)
    
    extract_from_node(classification_data)
    return taxonomy

def load_image_from_url_bytes_fast(url: str) -> Optional[bytes]:
    """Load image from URL and return bytes - optimized"""
    try:
        headers = {
            'User-Agent': 'MarineScopeApp/1.0',
            'Accept': 'image/*'
        }
        
        # Fix common URL issues
        if url.startswith('//'):
            url = 'https:' + url
        elif url.startswith('http://'):
            url = url.replace('http://', 'https://')
        
        # Handle Wikipedia thumbnail URLs
        if '/thumb/' in url and ('wikipedia.org' in url or 'wikimedia.org' in url):
            try:
                # Try to get original image
                if '/thumb/' in url:
                    parts = url.split('/thumb/')
                    if len(parts) > 1:
                        thumb_part = parts[1]
                        if '/' in thumb_part:
                            subparts = thumb_part.split('/')
                            if len(subparts) > 1:
                                original_path = '/'.join(subparts[:-1])
                                original_url = f"https://upload.wikimedia.org/wikipedia/commons/{original_path}"
                                # Try original image first
                                try:
                                    resp = requests.get(original_url, timeout=5, headers=headers)
                                    if resp.status_code == 200 and resp.headers.get('content-type', '').startswith('image/'):
                                        return resp.content
                                except:
                                    pass
            except Exception:
                pass
        
        # Try the given URL
        resp = requests.get(url, timeout=5, headers=headers)
        
        if resp.status_code == 200:
            content_type = resp.headers.get('content-type', '')
            if content_type.startswith('image/'):
                return resp.content
        
        return None
        
    except:
        return None

def pil_bytes_to_qpixmap_fast(b: bytes, size: Tuple[int, int] = (320, 240)) -> QPixmap:
    """Convert PIL image bytes to QPixmap - optimized"""
    try:
        image = Image.open(io.BytesIO(b))
        
        # Convert to RGBA if needed
        if image.mode not in ('RGBA', 'RGB'):
            image = image.convert('RGBA')
        elif image.mode == 'RGB':
            image = image.convert('RGBA')
        
        # Scale while maintaining aspect ratio
        image.thumbnail(size, Image.Resampling.LANCZOS)
        
        # Convert to QPixmap
        if image.mode == 'RGBA':
            data = image.tobytes("raw", "RGBA")
            qimg = QImage(data, image.width, image.height, QImage.Format.Format_RGBA8888)
        elif image.mode == 'RGB':
            data = image.tobytes("raw", "RGB")
            qimg = QImage(data, image.width, image.height, QImage.Format.Format_RGB888)
        else:
            image = image.convert('RGBA')
            data = image.tobytes("raw", "RGBA")
            qimg = QImage(data, image.width, image.height, QImage.Format.Format_RGBA8888)
        
        pix = QPixmap.fromImage(qimg)
        return pix
    except Exception as e:
        return QPixmap()

# ==================== INITIALIZE HIGH-LEVEL TAXA ====================
def initialize_high_level_taxa():
    """Initialize high-level taxa after all dependencies are loaded"""
    global HIGH_LEVEL_TAXA
    HIGH_LEVEL_TAXA = fetch_high_level_taxa_cached()

# ==================== OPTIMIZED BROWSE FUNCTION ====================
def browse_marine_animals_fast(offset: int = 0, limit: int = 20) -> List[Dict[str, Any]]:
    """Fast browsing of marine animals from WoRMS"""
    marine_species = []
    
    print(f">>> DEBUG: Fast browsing starting at offset {offset}, limit {limit}")
    
    # Define popular marine animal groups to browse
    popular_marine_groups = [
        "whale", "dolphin", "shark", "ray", "turtle", "seal", 
        "octopus", "crab", "jellyfish", "starfish", "coral"
    ]
    
    # Also try scientific names of popular groups
    scientific_groups = [
        "Orcinus orca", "Delphinus delphis", "Carcharodon carcharias",
        "Chelonia mydas", "Phoca vitulina", "Octopus vulgaris"
    ]
    
    # Combine all search terms
    all_search_terms = popular_marine_groups + scientific_groups
    
    # Shuffle to get variety
    random.shuffle(all_search_terms)
    
    # Track which species we've already found
    seen_aphia_ids = set()
    
    for search_term in all_search_terms:
        if len(marine_species) >= (offset + limit):
            break
        
        try:
            # Search for this term
            search_results = search_worms_species_fast(search_term)
            
            for species_data in search_results:
                aphia_id = species_data.get('aphia_id')
                
                # Skip if we've already seen this species
                if not aphia_id or aphia_id in seen_aphia_ids:
                    continue
                
                # Only add if we've reached the offset
                if len(marine_species) >= offset:
                    marine_species.append(species_data)
                    seen_aphia_ids.add(aphia_id)
                
                # Stop if we have enough
                if len(marine_species) >= (offset + limit):
                    break
            
            # Small delay to avoid overwhelming the API
            time.sleep(0.3)  # Reduced
            
        except Exception as e:
            continue
    
    print(f">>> DEBUG: Fast browsing found {len(marine_species)} species")
    
    # Return only the requested slice
    start_idx = min(offset, len(marine_species))
    end_idx = min(offset + limit, len(marine_species))
    return marine_species[start_idx:end_idx]

# ==================== THREAD CLASSES ====================
class MarineSearchThread(QThread):
    """Thread for searching marine species"""
    finished = pyqtSignal(list)
    error = pyqtSignal(str)
    progress = pyqtSignal(str)
    
    def __init__(self, query: str = "", browse_mode: bool = False, browse_offset: int = 0, browse_limit: int = BROWSE_LIMIT_INITIAL):
        super().__init__()
        self.query = query
        self.browse_mode = browse_mode
        self.browse_offset = browse_offset
        self.browse_limit = browse_limit
    
    def run(self):
        """Main thread execution"""
        try:
            if self.browse_mode:
                results = self.browse_marine_animals()
            else:
                results = self.search_marine_species(self.query)
            
            self.finished.emit(results)
            
        except Exception as e:
            self.error.emit(str(e))
    
    def browse_marine_animals(self) -> List[Dict[str, Any]]:
        """Browse marine animals using fast search"""
        self.progress.emit(f"Browsing marine animals...")
        
        # Use the fast browsing function
        marine_species = browse_marine_animals_fast(
            offset=self.browse_offset,
            limit=self.browse_limit
        )
        
        return marine_species
    
    def search_marine_species(self, query: str) -> List[Dict[str, Any]]:
        """Search for marine species - optimized"""
        print(f">>> Thread: Searching for '{query}'")
        
        # For empty or very short queries, just return empty
        if not query or len(query.strip()) < 2:
            print(f">>> Thread: Query too short, returning empty")
            return []
        
        self.progress.emit(f"Searching WoRMS...")
        
        # Call the fast search function
        results = search_worms_species_fast(query)
        
        if results:
            print(f">>> Thread: Found {len(results)} results")
            return results
        else:
            print(f">>> Thread: No results found for '{query}'")
            return []

# ==================== UI COMPONENTS ====================
class SpeciesListItem(QWidget):
    """Custom widget for species list items"""
    clicked = pyqtSignal()
    
    def __init__(self, species_data: Dict[str, Any], parent=None):
        super().__init__(parent)
        self.species_data = species_data
        self.is_selected = False
        self.init_ui()
        
    def init_ui(self):
        layout = QVBoxLayout()
        layout.setSpacing(4)
        layout.setContentsMargins(10, 8, 6, 8)
        
        # Scientific name (bold)
        sci_name = self.species_data.get('latin_name') or self.species_data.get('title', 'Unknown')
        sci_label = QLabel(f"<b>{sci_name}</b>")
        sci_label.setStyleSheet(f"color: {TEXT_COLOR}; font-size: 13px;")
        sci_label.setWordWrap(True)
        layout.addWidget(sci_label)
        
        # Common name
        common_name = self.species_data.get('common_name', '')
        if common_name and common_name != sci_name:
            common_label = QLabel(common_name)
            common_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 11px;")
            common_label.setWordWrap(True)
            layout.addWidget(common_label)
        
        # Status indicators
        status_layout = QHBoxLayout()
        status_layout.setSpacing(6)
        
        if self.species_data.get('is_marine'):
            marine_icon = QLabel("🌊")
            marine_icon.setToolTip("Marine species")
            status_layout.addWidget(marine_icon)
        
        if self.species_data.get('is_brackish'):
            brackish_icon = QLabel("💧")
            brackish_icon.setToolTip("Brackish water species")
            status_layout.addWidget(brackish_icon)
            
        if self.species_data.get('is_freshwater'):
            fresh_icon = QLabel("💦")
            fresh_icon.setToolTip("Freshwater species")
            status_layout.addWidget(fresh_icon)
        
        if self.species_data.get('source') == 'local':
            user_icon = QLabel("⭐")
            user_icon.setToolTip("User-added species")
            status_layout.addWidget(user_icon)
        
        status_layout.addStretch()
        layout.addLayout(status_layout)
        
        # Aphia ID if available
        aphia_id = self.species_data.get('aphia_id')
        if aphia_id:
            id_label = QLabel(f"AphiaID: {aphia_id}")
            id_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px; font-family: monospace;")
            layout.addWidget(id_label)
        
        self.setLayout(layout)
        self.update_style()
        
    def update_style(self):
        if self.is_selected:
            self.setStyleSheet(f"""
                SpeciesListItem {{
                    background: {SECONDARY_COLOR}20;
                    border: 2px solid {SECONDARY_COLOR};
                    border-right: none;
                    border-top-right-radius: 0px;
                    border-bottom-right-radius: 0px;
                    border-top-left-radius: 6px;
                    border-bottom-left-radius: 6px;
                    margin: 2px 0px 2px 2px;
                }}
                SpeciesListItem * {{
                    background: transparent;
                    border: none;
                    border-radius: 0px;
                }}
            """)
        else:
            self.setStyleSheet(f"""
                SpeciesListItem {{
                    background: {'white' if not IS_DARK_MODE else DARK_BG};
                    border: 1px solid {BORDER_COLOR};
                    border-right: none;
                    border-top-right-radius: 0px;
                    border-bottom-right-radius: 0px;
                    border-top-left-radius: 6px;
                    border-bottom-left-radius: 6px;
                    margin: 2px 0px 2px 2px;
                }}
                SpeciesListItem:hover {{
                    background: {LIGHT_BG if not IS_DARK_MODE else LIGHT_BG};
                    border: 1px solid {SECONDARY_COLOR};
                    border-right: none;
                    border-top-right-radius: 0px;
                    border-bottom-right-radius: 0px;
                    border-top-left-radius: 6px;
                    border-bottom-left-radius: 6px;
                }}
                SpeciesListItem * {{
                    background: transparent;
                    border: none;
                    border-radius: 0px;
                }}
            """)
    
    def mousePressEvent(self, event):
        self.clicked.emit()
        event.accept()
    
    def set_selected(self, selected: bool):
        self.is_selected = selected
        self.update_style()

class InfoBadge(QFrame):
    """Styled badge for displaying key information"""
    def __init__(self, text: str, color: str = SECONDARY_COLOR, parent=None):
        super().__init__(parent)
        self.update_style(color)
        
        layout = QHBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        self.label = QLabel(text)
        layout.addWidget(self.label)
        self.setLayout(layout)
        self.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
    
    def update_style(self, color: str):
        self.setStyleSheet(f"""
            InfoBadge {{
                background: {color}20;
                border: 1px solid {color}40;
                border-radius: 12px;
                padding: 4px 10px;
                color: {color};
                font-size: 11px;
                font-weight: bold;
            }}
        """)

class DepthVisualization(QWidget):
    """Simple depth visualization widget"""
    def __init__(self, min_depth: float, max_depth: float, avg_depth: float, parent=None):
        super().__init__(parent)
        self.min_depth = min_depth
        self.max_depth = max_depth
        self.avg_depth = avg_depth
        self.init_ui()
        
    def init_ui(self):
        layout = QVBoxLayout()
        layout.setSpacing(4)
        
        title = QLabel("Depth Range")
        title.setStyleSheet(f"color: {TEXT_COLOR}; font-weight: bold;")
        layout.addWidget(title)
        
        viz_widget = QWidget()
        viz_widget.setFixedHeight(60)
        viz_widget.setObjectName("depthViz")
        viz_widget.setStyleSheet(f"""
            QWidget#depthViz {{
                background: qlineargradient(x1:0, y1:0, x2:0, y2:1,
                    stop:0 #87CEEB, stop:0.3 #1E90FF, stop:0.7 #00008B, stop:1 #000033);
                border-radius: 4px;
                border: 1px solid {BORDER_COLOR};
            }}
        """)
        layout.addWidget(viz_widget)
        
        labels_layout = QHBoxLayout()
        min_label = QLabel(f"{int(self.min_depth):,} m")
        min_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px;")
        labels_layout.addWidget(min_label)
        labels_layout.addStretch()
        
        avg_label = QLabel(f"Avg: {int(self.avg_depth):,} m")
        avg_label.setStyleSheet(f"color: {TEXT_COLOR}; font-size: 10px; font-weight: bold;")
        labels_layout.addWidget(avg_label)
        labels_layout.addStretch()
        
        max_label = QLabel(f"{int(self.max_depth):,} m")
        max_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px;")
        labels_layout.addWidget(max_label)
        labels_layout.addStretch()
        
        layout.addLayout(labels_layout)
        
        if self.avg_depth < 200:
            zone = "Epipelagic (Sunlight Zone)"
        elif self.avg_depth < 1000:
            zone = "Mesopelagic (Twilight Zone)"
        elif self.avg_depth < 4000:
            zone = "Bathypelagic (Midnight Zone)"
        else:
            zone = "Abyssopelagic (Abyss)"
            
        zone_label = QLabel(zone)
        zone_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 10px; font-style: italic;")
        zone_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(zone_label)
        
        self.setLayout(layout)

class OceanBasinPills(QWidget):
    """Display ocean basins as pills"""
    def __init__(self, basins: List[str], parent=None):
        super().__init__(parent)
        self.basins = basins
        self.init_ui()
        
    def init_ui(self):
        layout = QVBoxLayout()
        layout.setSpacing(6)
        
        title = QLabel("Ocean Basins")
        title.setStyleSheet(f"color: {TEXT_COLOR}; font-weight: bold;")
        layout.addWidget(title)
        
        # Create a widget that will contain multiple rows of pills
        pills_container = QWidget()
        pills_layout = QVBoxLayout(pills_container)
        pills_layout.setSpacing(6)
        pills_layout.setContentsMargins(0, 0, 0, 0)
        
        # Group basins into rows of 2
        for i in range(0, len(self.basins), 2):
            row_basins = self.basins[i:i+2]
            row_widget = QWidget()
            row_layout = QHBoxLayout(row_widget)
            row_layout.setSpacing(6)
            row_layout.setContentsMargins(0, 0, 0, 0)
            
            for basin in row_basins:
                pill = InfoBadge(basin, ACCENT_COLOR)
                row_layout.addWidget(pill)
            
            row_layout.addStretch()
            pills_layout.addWidget(row_widget)
        
        layout.addWidget(pills_container)
        self.setLayout(layout)

class LoadingOverlay(QWidget):
    """Overlay that shows loading progress"""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.init_ui()
        self.update_style()
        
    def init_ui(self):
        layout = QVBoxLayout()
        layout.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
        self.spinner = QLabel("⏳")
        self.spinner.setStyleSheet("font-size: 32px;")
        layout.addWidget(self.spinner)
        
        self.status_label = QLabel("Initializing...")
        self.status_label.setStyleSheet(f"color: {TEXT_COLOR}; font-weight: bold;")
        layout.addWidget(self.status_label)
        
        self.detail_label = QLabel("")
        self.detail_label.setStyleSheet(f"color: {TEXT_SECONDARY};")
        layout.addWidget(self.detail_label)
        
        self.setLayout(layout)
        
    def update_style(self):
        """Update the style based on current theme"""
        # Use global theme variables
        if IS_DARK_MODE:
            bg_color = "rgba(44, 62, 80, 0.9)"  # Dark mode background
            text_color = DARK_TEXT_COLOR
            text_secondary = DARK_TEXT_SECONDARY
        else:
            bg_color = "rgba(255, 255, 255, 0.9)"  # Light mode background
            text_color = LIGHT_TEXT_COLOR
            text_secondary = LIGHT_TEXT_SECONDARY
        
        self.setStyleSheet(f"""
            LoadingOverlay {{
                background: {bg_color};
                border-radius: 10px;
            }}
        """)
        
        # Update label colors
        self.status_label.setStyleSheet(f"color: {text_color}; font-weight: bold;")
        self.detail_label.setStyleSheet(f"color: {text_secondary};")
        
    def update_status(self, status: str, detail: str = ""):
        self.status_label.setText(status)
        self.detail_label.setText(detail)
        spinners = ["⏳", "⌛", "⏳", "⌛"]
        current = self.spinner.text()
        idx = (spinners.index(current) + 1) % len(spinners) if current in spinners else 0
        self.spinner.setText(spinners[idx])

# ==================== DIALOGS ====================
class NewSpeciesDialog(QDialog):
    """Dialog for adding new species"""
    def __init__(self, parent=None, species_name: Optional[str] = None):
        super().__init__(parent)
        self.setWindowTitle("Add New Species")
        self.setModal(True)
        self.setMinimumWidth(420)
        
        # Main layout
        main_layout = QVBoxLayout()
        
        # Form layout for species details
        form_layout = QFormLayout()
        
        self.name_input = QLineEdit()
        if species_name:
            self.name_input.setText(species_name)
        self.latin_name_input = QLineEdit()
        self.habitat_input = QLineEdit()
        self.place_input = QLineEdit()
        self.depth_input = QSpinBox()
        self.depth_input.setRange(0, 20000)
        self.description_input = QTextEdit()
        self.image_path = None
        
        form_layout.addRow("Common Name:", self.name_input)
        form_layout.addRow("Latin Name:", self.latin_name_input)
        form_layout.addRow("Habitat:", self.habitat_input)
        form_layout.addRow("Place Found:", self.place_input)
        form_layout.addRow("Depth (meters):", self.depth_input)
        form_layout.addRow("Description:", self.description_input)
        
        main_layout.addLayout(form_layout)
        
        # Image section
        image_group = QGroupBox("Species Image")
        image_layout = QVBoxLayout()
        
        # Image preview
        self.image_preview = QLabel("No image selected")
        self.image_preview.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.image_preview.setMinimumHeight(150)
        self.image_preview.setStyleSheet(f"""
            QLabel {{
                border: 2px dashed {BORDER_COLOR};
                border-radius: 8px;
                color: {TEXT_SECONDARY};
            }}
        """)
        image_layout.addWidget(self.image_preview)
        
        # Add image button
        self.add_image_btn = QPushButton("📸 Add Image")
        self.add_image_btn.clicked.connect(self.on_add_image)
        self.add_image_btn.setStyleSheet(f"""
            QPushButton {{
                background: {ACCENT_COLOR};
                color: white;
                font-weight: bold;
                padding: 8px;
                border-radius: 6px;
                border: 1px solid {ACCENT_COLOR};
            }}
            QPushButton:hover {{
                background: {ACCENT_COLOR}dd;
            }}
        """)
        image_layout.addWidget(self.add_image_btn)
        
        image_group.setLayout(image_layout)
        main_layout.addWidget(image_group)
        
        # Buttons
        btns = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        btns.accepted.connect(self.accept)
        btns.rejected.connect(self.reject)
        
        main_layout.addWidget(btns)
        
        self.setLayout(main_layout)
    
    def on_add_image(self):
        """Open file dialog to select an image"""
        file_path, _ = QFileDialog.getOpenFileName(
            self, 
            "Select Species Image", 
            "", 
            "Image Files (*.png *.jpg *.jpeg *.bmp *.gif)"
        )
        
        if file_path:
            self.image_path = file_path
            try:
                # Load and display preview
                pixmap = QPixmap(file_path)
                if not pixmap.isNull():
                    # Scale for preview
                    pixmap = pixmap.scaled(300, 200, 
                                        Qt.AspectRatioMode.KeepAspectRatio,
                                        Qt.TransformationMode.SmoothTransformation)
                    self.image_preview.setPixmap(pixmap)
                    self.image_preview.setText("")
            except Exception as e:
                print(f">>> DEBUG: Error loading image: {e}")
                self.image_preview.setText("Error loading image")
    
    def get_data(self) -> Optional[Dict[str, Any]]:
        if not self.name_input.text().strip():
            return None
        
        data = {
            'name': self.name_input.text().strip(),
            'latin_name': self.latin_name_input.text().strip(),
            'habitat': self.habitat_input.text().strip(),
            'place_found': self.place_input.text().strip(),
            'depth_found_meters': int(self.depth_input.value()),
            'description': self.description_input.toPlainText().strip(),
            'image_path': self.image_path,
            'is_user_created': True,
            'source': 'local',
            'common_name': self.name_input.text().strip(),
            'title': self.name_input.text().strip(),
            'aphia_id': None,
            'is_marine': True,
            'is_brackish': False,
            'is_freshwater': False,
            'is_terrestrial': False,
            'extract': self.description_input.toPlainText().strip() or "User-added species."
        }
        
        return data

# ==================== MAIN WINDOW ====================
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("MarineScope — Marine Animal Explorer")
        self.setMinimumSize(1200, 800)
        self.showMaximized()
        
        # Central widget
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        
        main_layout = QHBoxLayout(central_widget)
        main_layout.setSpacing(2)
        main_layout.setContentsMargins(2, 2, 2, 2)
        
        # ===== LEFT PANEL: Species Navigation =====
        left_panel = QWidget()
        left_panel.setMinimumWidth(320)
        left_panel.setMaximumWidth(380)
        left_layout = QVBoxLayout(left_panel)
        left_layout.setSpacing(8)
        left_layout.setContentsMargins(0, 0, 0, 0)
        
        # Search section
        search_group = QGroupBox("Search Marine Animals")
        search_group.setObjectName("searchGroup")
        search_layout = QVBoxLayout()
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Scientific name, common name, or AphiaID...")
        self.search_input.returnPressed.connect(self.on_search)
        search_layout.addWidget(self.search_input)
        
        search_buttons = QHBoxLayout()
        self.search_button = QPushButton("🔍 Search")
        self.search_button.clicked.connect(self.on_search)
        self.browse_button = QPushButton("🌊 Browse All")
        self.browse_button.clicked.connect(self.on_browse_all)
        search_buttons.addWidget(self.search_button)
        search_buttons.addWidget(self.browse_button)
        search_layout.addLayout(search_buttons)
        
        search_group.setLayout(search_layout)
        left_layout.addWidget(search_group)
        
        # Species list
        list_group = QGroupBox("Marine Animals")
        list_group.setObjectName("listGroup")
        
        list_layout = QVBoxLayout()
        list_layout.setContentsMargins(2, 2, 2, 2)
        list_layout.setSpacing(0)
        
        self.list_widget = QListWidget()
        self.list_widget.setAlternatingRowColors(False)
        self.list_widget.setObjectName("speciesList")
        self.list_widget.setVerticalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
        self.list_widget.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.list_widget.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOn)
        self.list_widget.setSpacing(0)
        list_layout.addWidget(self.list_widget)
        
        self.results_count = QLabel("0 marine animals")
        self.results_count.setObjectName("resultsCount")
        self.results_count.setAlignment(Qt.AlignmentFlag.AlignRight)
        list_layout.addWidget(self.results_count)
        
        # Browse More button (initially hidden)
        self.browse_more_btn = QPushButton("🌊 Browse More (5 more)")
        self.browse_more_btn.clicked.connect(self.on_browse_more)
        self.browse_more_btn.setObjectName("browseMoreBtn")
        self.browse_more_btn.hide()
        list_layout.addWidget(self.browse_more_btn)
        
        list_group.setLayout(list_layout)
        left_layout.addWidget(list_group, 1)
        
        # Action buttons
        action_layout = QVBoxLayout()
        action_layout.setSpacing(6)
        
        self.add_btn = QPushButton("➕ Add New Species")
        self.add_btn.clicked.connect(self.on_add_manual)
        self.add_btn.setObjectName("addBtn")
        action_layout.addWidget(self.add_btn)
        
        # Delete button for user-added species
        self.delete_btn = QPushButton("🗑️ Delete Selected")
        self.delete_btn.clicked.connect(self.on_delete_selected)
        self.delete_btn.setObjectName("deleteBtn")
        self.delete_btn.setEnabled(False)
        action_layout.addWidget(self.delete_btn)
        
        left_layout.addLayout(action_layout)
        main_layout.addWidget(left_panel)
        
        # ===== CENTER PANEL: Species Overview =====
        center_panel = QWidget()
        center_layout = QVBoxLayout(center_panel)
        center_layout.setSpacing(12)
        
        # Header with dark mode button
        header_container = QWidget()
        header_container.setMaximumHeight(50)
        header_layout = QHBoxLayout(header_container)
        header_layout.setContentsMargins(0, 0, 0, 0)
        
        # Left side: Species name
        self.name_label = QLabel("Select a marine animal")
        self.name_label.setObjectName("nameLabel")
        header_layout.addWidget(self.name_label, 1)
        
        # Center: Aphia ID
        self.aphia_id_label = QLabel("")
        self.aphia_id_label.setObjectName("aphiaIdLabel")
        header_layout.addWidget(self.aphia_id_label, 0, Qt.AlignmentFlag.AlignCenter)
        
        # Right side: Dark mode button
        button_container = QWidget()
        button_layout = QHBoxLayout(button_container)
        button_layout.setContentsMargins(0, 0, 0, 0)
        
        self.theme_toggle_btn = QPushButton("🌙")
        self.theme_toggle_btn.setFixedSize(30, 30)
        self.theme_toggle_btn.setObjectName("themeToggleBtn")
        self.theme_toggle_btn.clicked.connect(self.toggle_theme)
        self.theme_toggle_btn.setToolTip("Toggle dark/light mode")
        button_layout.addWidget(self.theme_toggle_btn, 0, Qt.AlignmentFlag.AlignRight)
        
        header_layout.addWidget(button_container, 1)
        
        center_layout.addWidget(header_container)
        
        # Image and quick facts
        overview_widget = QWidget()
        overview_layout = QHBoxLayout(overview_widget)
        overview_layout.setSpacing(20)
        
        # Image section
        image_container = QWidget()
        image_layout = QVBoxLayout(image_container)
        self.image_frame = QFrame()
        self.image_frame.setFrameShape(QFrame.Shape.Box)
        self.image_frame.setObjectName("imageFrame")
        self.image_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        frame_layout = QVBoxLayout(self.image_frame)
        frame_layout.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
        # Create container for image and add button
        self.image_container_widget = QWidget()
        self.image_container_layout = QVBoxLayout(self.image_container_widget)
        self.image_container_layout.setContentsMargins(0, 0, 0, 0)
        self.image_container_layout.setSpacing(0)
        
        self.image_label = QLabel()
        self.image_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.image_label.setText("📷\nNo image available")
        self.image_label.setObjectName("imageLabel")
        self.image_label.setWordWrap(True)
        self.image_label.setScaledContents(False)
        self.image_container_layout.addWidget(self.image_label, 1)
        
        # Add image button (initially hidden)
        self.add_image_btn = QPushButton("📸 Add Image")
        self.add_image_btn.setObjectName("addImageBtn")
        self.add_image_btn.clicked.connect(self.on_add_image_to_species)
        self.add_image_btn.hide()
        self.image_container_layout.addWidget(self.add_image_btn, 0, Qt.AlignmentFlag.AlignCenter)
        
        frame_layout.addWidget(self.image_container_widget)
        image_layout.addWidget(self.image_frame)
        self.image_source = QLabel("")
        self.image_source.setObjectName("imageSource")
        self.image_source.setAlignment(Qt.AlignmentFlag.AlignCenter)
        image_layout.addWidget(self.image_source)
        overview_layout.addWidget(image_container)
        
        # Quick facts
        facts_container = QWidget()
        facts_layout = QVBoxLayout(facts_container)
        facts_layout.setSpacing(12)
        
        self.sci_name_label = QLabel("")
        self.sci_name_label.setObjectName("sciNameLabel")
        facts_layout.addWidget(self.sci_name_label)
        
        self.status_container = QWidget()
        self.status_layout = QHBoxLayout(self.status_container)
        self.status_layout.setSpacing(8)
        facts_layout.addWidget(self.status_container)
        
        self.habitat_label = QLabel("")
        self.habitat_label.setObjectName("habitatLabel")
        facts_layout.addWidget(self.habitat_label)
        
        self.depth_widget = QWidget()
        self.depth_layout = QVBoxLayout(self.depth_widget)
        facts_layout.addWidget(self.depth_widget)
        
        self.basins_widget = QWidget()
        self.basins_layout = QVBoxLayout(self.basins_widget)
        facts_layout.addWidget(self.basins_widget)
        
        self.sources_label = QLabel("📊 Data Sources:")
        self.sources_label.setObjectName("sourcesLabel")
        facts_layout.addWidget(self.sources_label)
        
        self.sources_container = QWidget()
        self.sources_layout = QHBoxLayout(self.sources_container)
        self.sources_layout.setSpacing(6)
        facts_layout.addWidget(self.sources_container)
        
        facts_layout.addStretch()
        overview_layout.addWidget(facts_container, 1)
        
        center_layout.addWidget(overview_widget)
        
        # ===== RIGHT PANEL: Detailed Information =====
        self.tab_widget = QTabWidget()
        self.tab_widget.setMaximumWidth(450)
        self.tab_widget.setObjectName("tabWidget")
        
        # Tab 1: Taxonomy
        taxonomy_tab = QWidget()
        taxonomy_layout = QVBoxLayout(taxonomy_tab)
        taxonomy_layout.setSpacing(8)
        taxonomy_layout.setContentsMargins(8, 8, 8, 8)
        
        taxonomy_group = QGroupBox("Taxonomic Classification")
        taxonomy_group.setObjectName("taxonomyGroup")
        form_layout = QFormLayout()
        form_layout.setSpacing(4)
        form_layout.setContentsMargins(8, 12, 8, 8)
        self.taxonomy_labels = {}
        for rank in ["Kingdom", "Phylum", "Class", "Order", "Family", "Genus", "Species"]:
            label = QLabel("—")
            label.setObjectName(f"taxonomyLabel{rank}")
            form_layout.addRow(f"{rank}:", label)
            self.taxonomy_labels[rank.lower()] = label
        taxonomy_group.setLayout(form_layout)
        taxonomy_layout.addWidget(taxonomy_group)
        
        self.taxonomy_notes = QLabel("")
        self.taxonomy_notes.setObjectName("taxonomyNotes")
        self.taxonomy_notes.setWordWrap(True)
        taxonomy_layout.addWidget(self.taxonomy_notes)
        taxonomy_layout.addStretch()
        self.tab_widget.addTab(taxonomy_tab, "🧬 Taxonomy")
        
        # Tab 2: Habitat & Environment
        habitat_tab = QWidget()
        habitat_layout = QVBoxLayout(habitat_tab)
        habitat_layout.setSpacing(8)
        habitat_layout.setContentsMargins(8, 8, 8, 8)
        
        depth_group = QGroupBox("Depth Information")
        depth_group.setObjectName("depthGroup")
        depth_group_layout = QVBoxLayout()
        depth_group_layout.setContentsMargins(8, 12, 8, 8)
        self.depth_details = QLabel("")
        self.depth_details.setObjectName("depthDetails")
        self.depth_details.setWordWrap(True)
        depth_group_layout.addWidget(self.depth_details)
        depth_group.setLayout(depth_group_layout)
        habitat_layout.addWidget(depth_group)
        
        env_group = QGroupBox("Environmental Preferences")
        env_group.setObjectName("envGroup")
        env_layout = QVBoxLayout()
        env_layout.setContentsMargins(8, 12, 8, 8)
        self.environment_details = QLabel("")
        self.environment_details.setObjectName("environmentDetails")
        self.environment_details.setWordWrap(True)
        env_layout.addWidget(self.environment_details)
        env_group.setLayout(env_layout)
        habitat_layout.addWidget(env_group)
        habitat_layout.addStretch()
        self.tab_widget.addTab(habitat_tab, "🌊 Habitat")
        
        # Tab 3: Distribution
        distribution_tab = QWidget()
        distribution_layout = QVBoxLayout(distribution_tab)
        distribution_layout.setSpacing(8)
        distribution_layout.setContentsMargins(8, 8, 8, 8)
        
        dist_group = QGroupBox("Geographic Distribution")
        dist_group.setObjectName("distGroup")
        dist_layout = QVBoxLayout()
        dist_layout.setContentsMargins(8, 12, 8, 8)
        dist_layout.setSpacing(4)
        
        self.distribution_text = QTextEdit()
        self.distribution_text.setReadOnly(True)
        self.distribution_text.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.distribution_text.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.distribution_text.setObjectName("distributionText")
        
        # Set initial height
        self.distribution_text.setMinimumHeight(60)
        self.distribution_text.setMaximumHeight(500)
        
        # Enable word wrap
        self.distribution_text.setWordWrapMode(QTextOption.WrapMode.WordWrap)
        self.distribution_text.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        
        # Set alignment to top-left
        self.distribution_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        
        # Reduce top margin
        self.distribution_text.document().setDocumentMargin(4)
        
        dist_layout.addWidget(self.distribution_text, 1)
        
        # Data source label
        self.distribution_source_label = QLabel("Data source: WoRMS/OBIS")
        self.distribution_source_label.setStyleSheet(f"color: {TEXT_SECONDARY}; font-size: 9px; font-style: italic;")
        self.distribution_source_label.setAlignment(Qt.AlignmentFlag.AlignRight)
        dist_layout.addWidget(self.distribution_source_label)
        
        dist_group.setLayout(dist_layout)
        distribution_layout.addWidget(dist_group, 1)
        
        self.tab_widget.addTab(distribution_tab, "🗺️ Distribution")
        
        # Tab 4: Occurrence Data
        occurrence_tab = QWidget()
        occurrence_layout = QVBoxLayout(occurrence_tab)
        occurrence_layout.setSpacing(8)
        occurrence_layout.setContentsMargins(8, 8, 8, 8)
        
        stats_group = QGroupBox("Occurrence Statistics")
        stats_group.setObjectName("statsGroup")
        stats_form = QFormLayout()
        stats_form.setSpacing(4)
        stats_form.setContentsMargins(8, 12, 8, 8)
        self.occurrence_stats = {}
        for stat in ["Total Records", "Year Range", "With Depth Data", "With Coordinates", "Data Quality"]:
            label = QLabel("—")
            label.setObjectName(f"occurrenceStat{stat.replace(' ', '')}")
            stats_form.addRow(f"{stat}:", label)
            self.occurrence_stats[stat.lower().replace(" ", "_")] = label
        stats_group.setLayout(stats_form)
        occurrence_layout.addWidget(stats_group)
        
        quality_group = QGroupBox("Data Confidence")
        quality_group.setObjectName("qualityGroup")
        quality_layout = QVBoxLayout()
        quality_layout.setContentsMargins(8, 12, 8, 8)
        self.quality_bar = QProgressBar()
        self.quality_bar.setTextVisible(False)
        self.quality_bar.setMaximumHeight(10)
        self.quality_bar.setObjectName("qualityBar")
        quality_layout.addWidget(self.quality_bar)
        self.quality_label = QLabel("")
        self.quality_label.setObjectName("qualityLabel")
        quality_layout.addWidget(self.quality_label)
        quality_group.setLayout(quality_layout)
        occurrence_layout.addWidget(quality_group)
        occurrence_layout.addStretch()
        self.tab_widget.addTab(occurrence_tab, "📊 Data")
        
        # Tab 5: Description & Sources
        info_tab = QWidget()
        info_layout = QVBoxLayout(info_tab)
        info_layout.setSpacing(8)
        info_layout.setContentsMargins(8, 8, 8, 8)
        
        desc_group = QGroupBox("Description")
        desc_group.setObjectName("descGroup")
        desc_layout = QVBoxLayout()
        desc_layout.setContentsMargins(8, 12, 8, 8)
        desc_layout.setSpacing(0)
        
        self.description_text = QTextEdit()
        self.description_text.setReadOnly(True)
        self.description_text.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.description_text.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.description_text.setObjectName("descriptionText")
        
        # Set alignment to top-left
        self.description_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        
        # Enable word wrap and set wrap mode
        self.description_text.setWordWrapMode(QTextOption.WrapMode.WordWrap)
        self.description_text.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        
        # Set initial height
        self.description_text.setMinimumHeight(60)
        self.description_text.setMaximumHeight(1000)
        
        # Reduce top margin for better top alignment
        self.description_text.document().setDocumentMargin(4)
        
        desc_layout.addWidget(
    self.description_text,
    alignment=Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignHCenter
)       
        desc_group.setLayout(desc_layout)
        info_layout.addWidget(desc_group, 0)
        
        sources_group = QGroupBox("Data Sources, Citations")
        sources_group.setObjectName("sourcesGroup")
        sources_layout = QVBoxLayout()
        sources_layout.setContentsMargins(8, 12, 8, 8)
        sources_layout.setSpacing(0)
        
        self.sources_text = QTextEdit()
        self.sources_text.setReadOnly(True)
        self.sources_text.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.sources_text.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.sources_text.setObjectName("sourcesText")
        
        # Set alignment to top-left
        self.sources_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        
        # Enable word wrap and set wrap mode
        self.sources_text.setWordWrapMode(QTextOption.WrapMode.WordWrap)
        self.sources_text.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        
        # Set initial height
        self.sources_text.setMinimumHeight(40)
        self.sources_text.setMaximumHeight(500)
        
        # Reduce top margin for better top alignment
        self.sources_text.document().setDocumentMargin(4)
        
        sources_layout.addWidget(
    self.sources_text,
    alignment=Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignHCenter
)
        sources_group.setLayout(sources_layout)
        info_layout.addWidget(sources_group, 0)
        
        info_layout.addStretch()
        
        self.tab_widget.addTab(info_tab, "📝 Info")
        
        # Add panels to main layout
        center_panel_container = QWidget()
        center_panel_container.setLayout(center_layout)
        
        # Create a splitter layout with adjusted ratios
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.addWidget(center_panel_container)
        splitter.addWidget(self.tab_widget)
        
        splitter.setSizes([600, 350])
        
        main_layout.addWidget(splitter, 1)
        
        # Loading overlay
        self.loading_overlay = LoadingOverlay()
        self.loading_overlay.hide()
        main_layout.addWidget(self.loading_overlay)
        
        # Initialize data
        self.current_search_results = []
        self.user_species = load_user_species()
        self.current_species_data = None
        self.search_thread = None
        self.current_image_path = None
        self.selected_item_widget = None
        
        # Browsing state
        self.browse_offset = 0
        self.is_browsing = False
        
        # Apply theme after all widgets are created
        self.apply_theme()
        
        # Load initial data
        QTimer.singleShot(100, self.load_initial_marine_animals)

    def resizeEvent(self, event):
        """Handle window resize events to adjust text box heights"""
        super().resizeEvent(event)
        
        # Check if we have current species data
        try:
            if self.current_species_data:
                # Delay the recalculation slightly to ensure layout is complete
                QTimer.singleShot(100, lambda: self.adjust_text_box_heights())
        except AttributeError:
            # current_species_data doesn't exist yet, ignore
            pass
    
    def adjust_text_box_heights(self):
        """Adjust the heights of text boxes based on content"""
        # Use try-except to handle cases where current_species_data doesn't exist
        try:
            if self.current_species_data:
                # Update info tab text boxes
                self.update_info_tab(self.current_species_data)
                
                # Update distribution tab text box
                self.update_distribution_tab(self.current_species_data)
        except AttributeError:
            # current_species_data attribute doesn't exist yet
            pass

    def on_search(self):
        """Handle search button click or Enter key press"""
        query = self.search_input.text().strip()
        if not query:
            return
        
        # Clear browsing state
        self.is_browsing = False
        self.browse_offset = 0
        self.browse_more_btn.hide()
        
        # Start search
        self.show_loading("Searching for marine animals...")
        self.search_thread = MarineSearchThread(query=query)
        self.search_thread.finished.connect(self.handle_search_results)
        self.search_thread.error.connect(self.handle_search_error)
        self.search_thread.start()

    def on_browse_all(self):
        """Browse all marine animals"""
        self.search_input.clear()
        self.is_browsing = True
        self.browse_offset = 0
        
        self.show_loading("Browsing marine animals...")
        self.search_thread = MarineSearchThread(
            browse_mode=True,
            browse_offset=self.browse_offset,
            browse_limit=BROWSE_LIMIT_INITIAL
        )
        self.search_thread.finished.connect(self.handle_search_results)
        self.search_thread.error.connect(self.handle_search_error)
        self.search_thread.start()

    def on_browse_more(self):
        """Browse more marine animals"""
        if not self.is_browsing:
            return
        
        self.browse_offset += BROWSE_LIMIT_INCREMENT
        
        self.show_loading("Loading more marine animals...")
        self.search_thread = MarineSearchThread(
            browse_mode=True,
            browse_offset=self.browse_offset,
            browse_limit=BROWSE_LIMIT_INCREMENT
        )
        self.search_thread.finished.connect(self.handle_browse_more_results)
        self.search_thread.error.connect(self.handle_search_error)
        self.search_thread.start()

    def handle_search_results(self, results):
        """Handle search results"""
        self.hide_loading()
        self.current_search_results = results
        
        # Clear the list
        self.list_widget.clear()
        
        # Add all results to the list
        for species_data in results:
            self.add_species_to_list(species_data)
        
        # Update results count
        self.results_count.setText(f"{len(results)} marine animals")
        
        # Show browse more button if browsing
        if self.is_browsing and len(results) >= BROWSE_LIMIT_INITIAL:
            self.browse_more_btn.show()
        else:
            self.browse_more_btn.hide()
        
        # Select first item if available
        if results and self.list_widget.count() > 0:
            first_item = self.list_widget.item(0)
            if first_item:
                self.list_widget.setCurrentItem(first_item)
                widget = self.list_widget.itemWidget(first_item)
                if widget:
                    widget.set_selected(True)
                    self.selected_item_widget = widget
                    self.current_species_data = results[0]
                    self.display_species_details(results[0])

    def handle_browse_more_results(self, new_results):
        """Handle additional browse results"""
        self.hide_loading()
        
        if not new_results:
            return
        
        # Add to current results
        self.current_search_results.extend(new_results)
        
        # Add new items to list
        start_idx = len(self.current_search_results) - len(new_results)
        for i, species_data in enumerate(new_results):
            self.add_species_to_list(species_data)
        
        # Update results count
        self.results_count.setText(f"{len(self.current_search_results)} marine animals")
        
        # Keep browse more button visible
        if len(new_results) >= BROWSE_LIMIT_INCREMENT:
            self.browse_more_btn.show()
        else:
            self.browse_more_btn.hide()

    def handle_search_error(self, error_msg):
        """Handle search error"""
        self.hide_loading()
        QMessageBox.warning(self, "Search Error", f"An error occurred during search: {error_msg}")

    def add_species_to_list(self, species_data):
        """Add a species to the list widget"""
        item_widget = SpeciesListItem(species_data)
        item = QListWidgetItem()
        item.setSizeHint(item_widget.sizeHint())
        self.list_widget.addItem(item)
        self.list_widget.setItemWidget(item, item_widget)
        
        # Connect click signal
        item_widget.clicked.connect(lambda: self.on_species_clicked(item, item_widget, species_data))

    def on_species_clicked(self, item, widget, species_data):
        """Handle species item click"""
        # Deselect previously selected widget
        if self.selected_item_widget:
            self.selected_item_widget.set_selected(False)
        
        # Select current widget
        widget.set_selected(True)
        self.selected_item_widget = widget
        self.list_widget.setCurrentItem(item)
        
        # Display species details
        self.display_species_details(species_data)

    def show_loading(self, message=""):
        """Show loading overlay"""
        self.loading_overlay.update_status(message)
        self.loading_overlay.show()
        QApplication.processEvents()

    def hide_loading(self):
        """Hide loading overlay"""
        self.loading_overlay.hide()
        QApplication.processEvents()

    def load_initial_marine_animals(self):
        """Load initial marine animals for browsing"""
        self.on_browse_all()

    def on_add_manual(self):
        """Open dialog to add new species manually"""
        dialog = NewSpeciesDialog(self)
        if dialog.exec():
            species_data = dialog.get_data()
            if species_data:
                # Add to user species list
                self.user_species.append(species_data)
                save_user_species(self.user_species)
                
                # Add to current view
                self.add_species_to_list(species_data)
                self.current_search_results.append(species_data)
                self.results_count.setText(f"{len(self.current_search_results)} marine animals")
                
                # Show success message
                QMessageBox.information(self, "Success", "Species added successfully!")

    def on_delete_selected(self):
        """Delete selected user-added species"""
        if not self.selected_item_widget or not self.current_species_data:
            return
        
        species_data = self.current_species_data
        
        # Check if it's a user-added species
        if species_data.get('source') != 'local':
            QMessageBox.warning(self, "Cannot Delete", "Only user-added species can be deleted.")
            return
        
        # Confirm deletion
        reply = QMessageBox.question(
            self,
            "Confirm Delete",
            f"Are you sure you want to delete '{species_data.get('title', 'Unknown')}'?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No
        )
        
        if reply == QMessageBox.StandardButton.Yes:
            # Remove from user species
            self.user_species = [s for s in self.user_species if s.get('title') != species_data.get('title')]
            save_user_species(self.user_species)
            
            # Remove from current view
            self.current_search_results = [s for s in self.current_search_results if s.get('title') != species_data.get('title')]
            
            # Clear the list and reload
            self.list_widget.clear()
            for species in self.current_search_results:
                self.add_species_to_list(species)
            
            # Update results count
            self.results_count.setText(f"{len(self.current_search_results)} marine animals")
            
            # Clear details display
            self.clear_species_display()
            
            # Disable delete button
            self.delete_btn.setEnabled(False)

    def on_add_image_to_species(self):
        """Add image to current species"""
        if not self.current_species_data:
            return
        
        file_path, _ = QFileDialog.getOpenFileName(
            self, 
            "Select Image", 
            "", 
            "Image Files (*.png *.jpg *.jpeg *.bmp *.gif)"
        )
        
        if not file_path:
            return
        
        # Check if it's a user-added species
        if self.current_species_data.get('source') != 'local':
            QMessageBox.warning(self, "Cannot Modify", "Only user-added species can be modified.")
            return
        
        # Update the species data
        for i, species in enumerate(self.user_species):
            if species.get('title') == self.current_species_data.get('title'):
                self.user_species[i]['image_path'] = file_path
                break
        
        # Save and reload
        save_user_species(self.user_species)
        self.user_species = load_user_species()
        
        # Update current display
        self.display_species_details(self.current_species_data)
        QMessageBox.information(self, "Success", "Image updated successfully!")

    def display_species_details(self, species_data):
        """Display species details in the UI"""
        self.current_species_data = species_data
        
        # Update header
        common_name = species_data.get('common_name', '')
        scientific_name = species_data.get('latin_name', '')
        
        if common_name and common_name != scientific_name:
            self.name_label.setText(f"{common_name}")
        else:
            self.name_label.setText(scientific_name)
        
        # Update scientific name
        if scientific_name:
            self.sci_name_label.setText(f"{scientific_name}")
        else:
            self.sci_name_label.setText("")
        
        # Update Aphia ID
        aphia_id = species_data.get('aphia_id')
        if aphia_id:
            self.aphia_id_label.setText(f"AphiaID: {aphia_id}")
            self.aphia_id_label.show()
        else:
            self.aphia_id_label.hide()
        
        # Update image
        self.load_species_image(species_data)
        
        # Update status badges
        self.update_status_badges(species_data)
        
        # Update habitat
        habitat = species_data.get('habitat', 'Unknown')
        self.habitat_label.setText(f"🌍 Habitat: {habitat}")
        
        # Update depth info
        self.update_depth_info(species_data)
        
        # Update ocean basins
        self.update_ocean_basins(species_data)
        
        # Update sources
        self.update_sources(species_data)
        
        # Update taxonomy tab
        self.update_taxonomy_tab(species_data)
        
        # Update habitat tab
        self.update_habitat_tab(species_data)
        
        # Update distribution tab
        self.update_distribution_tab(species_data)
        
        # Update occurrence tab
        self.update_occurrence_tab(species_data)
        
        # Update info tab
        self.update_info_tab(species_data)
        
        # Enable/disable delete button
        self.delete_btn.setEnabled(species_data.get('source') == 'local')
        
        # Show/hide add image button
        self.add_image_btn.setVisible(species_data.get('source') == 'local')

    def clear_species_display(self):
        """Clear all species display fields"""
        self.name_label.setText("Select a marine animal")
        self.sci_name_label.setText("")
        self.aphia_id_label.hide()
        self.image_label.setText("📷\nNo image available")
        self.image_source.setText("")
        
        # Clear status container
        for i in reversed(range(self.status_layout.count())):
            widget = self.status_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        self.habitat_label.setText("")
        
        # Clear depth widget
        for i in reversed(range(self.depth_layout.count())):
            widget = self.depth_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        # Clear basins widget
        for i in reversed(range(self.basins_layout.count())):
            widget = self.basins_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        # Clear sources
        self.sources_label.hide()
        for i in reversed(range(self.sources_layout.count())):
            widget = self.sources_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        # Clear taxonomy tab
        for label in self.taxonomy_labels.values():
            label.setText("—")
        self.taxonomy_notes.setText("")
        
        # Clear habitat tab
        self.depth_details.setText("")
        self.environment_details.setText("")
        
        # Clear distribution tab
        self.distribution_text.clear()
        self.distribution_text.setFixedHeight(60)
        self.distribution_source_label.setText("Data source: None")
        
        # Clear occurrence tab
        for label in self.occurrence_stats.values():
            label.setText("—")
        self.quality_bar.setValue(0)
        self.quality_label.setText("")
        
        # Clear info tab
        self.description_text.clear()
        self.sources_text.clear()
        self.description_text.setFixedHeight(60)
        self.sources_text.setFixedHeight(40)

    def load_species_image(self, species_data):
        """Load and display species image"""
        # Try to load from local path first
        image_path = species_data.get('image_path')
        if image_path and os.path.exists(image_path):
            try:
                pixmap = QPixmap(image_path)
                if not pixmap.isNull():
                    pixmap = pixmap.scaled(320, 240, 
                                        Qt.AspectRatioMode.KeepAspectRatio,
                                        Qt.TransformationMode.SmoothTransformation)
                    self.image_label.setPixmap(pixmap)
                    self.image_source.setText("📁 Local file")
                    return
            except:
                pass
        
        # Try to load from URL
        thumb_url = species_data.get('thumb_url')
        if thumb_url:
            # Load image in background thread (simplified)
            QTimer.singleShot(0, lambda: self.load_image_from_url(thumb_url, species_data))
        else:
            self.image_label.setText("📷\nNo image available")
            self.image_source.setText("")

    def load_image_from_url(self, url, species_data):
        """Load image from URL"""
        try:
            image_bytes = load_image_from_url_bytes_fast(url)
            if image_bytes:
                pixmap = pil_bytes_to_qpixmap_fast(image_bytes)
                if not pixmap.isNull():
                    self.image_label.setPixmap(pixmap)
                    self.image_source.setText(f"📡 {species_data.get('image_source', 'External source')}")
                    return
        except:
            pass
        
        # Fallback
        self.image_label.setText("📷\nNo image available")
        self.image_source.setText("")

    def update_status_badges(self, species_data):
        """Update status badges"""
        # Clear existing badges
        for i in reversed(range(self.status_layout.count())):
            widget = self.status_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        # Add new badges
        if species_data.get('is_marine'):
            badge = InfoBadge("🌊 Marine", SECONDARY_COLOR)
            self.status_layout.addWidget(badge)
        
        if species_data.get('is_brackish'):
            badge = InfoBadge("💧 Brackish", ACCENT_COLOR)
            self.status_layout.addWidget(badge)
        
        if species_data.get('is_freshwater'):
            badge = InfoBadge("💦 Freshwater", SUCCESS_COLOR)
            self.status_layout.addWidget(badge)
        
        if species_data.get('is_terrestrial'):
            badge = InfoBadge("🌿 Terrestrial", WARNING_COLOR)
            self.status_layout.addWidget(badge)
        
        if species_data.get('source') == 'local':
            badge = InfoBadge("⭐ User-added", "#FFD700")
            self.status_layout.addWidget(badge)
        
        self.status_layout.addStretch()

    def update_depth_info(self, species_data):
        """Update depth information"""
        # Clear existing widgets
        for i in reversed(range(self.depth_layout.count())):
            widget = self.depth_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        depth_info = species_data.get('depth_info')
        if depth_info and 'avg_depth' in depth_info:
            title = QLabel("📏 Depth Range")
            title.setStyleSheet(f"color: {TEXT_COLOR}; font-weight: bold; margin-top: 10px;")
            self.depth_layout.addWidget(title)
            
            viz = DepthVisualization(
                depth_info.get('min_depth', 0),
                depth_info.get('max_depth', 0),
                depth_info.get('avg_depth', 0)
            )
            self.depth_layout.addWidget(viz)
        else:
            label = QLabel("📏 Depth: Unknown")
            label.setStyleSheet(f"color: {TEXT_SECONDARY};")
            self.depth_layout.addWidget(label)

    def update_ocean_basins(self, species_data):
        """Update ocean basins display"""
        # Clear existing widgets
        for i in reversed(range(self.basins_layout.count())):
            widget = self.basins_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        basins = species_data.get('ocean_basins', [])
        if basins:
            pills = OceanBasinPills(basins)
            self.basins_layout.addWidget(pills)
        else:
            label = QLabel("🌐 Ocean Basins: Unknown")
            label.setStyleSheet(f"color: {TEXT_SECONDARY};")
            self.basins_layout.addWidget(label)

    def update_sources(self, species_data):
        """Update sources display"""
        # Clear existing widgets
        for i in reversed(range(self.sources_layout.count())):
            widget = self.sources_layout.itemAt(i).widget()
            if widget:
                widget.deleteLater()
        
        sources = []
        
        # Add source badges
        if species_data.get('source') == 'worms_obis':
            badge = InfoBadge("WoRMS", SECONDARY_COLOR)
            self.sources_layout.addWidget(badge)
            sources.append("World Register of Marine Species (WoRMS)")
        
        if species_data.get('source') == 'local':
            badge = InfoBadge("Local", ACCENT_COLOR)
            self.sources_layout.addWidget(badge)
            sources.append("User database")
        
        if species_data.get('thumb_url'):
            if 'wikipedia' in species_data.get('thumb_url', ''):
                badge = InfoBadge("Wikipedia", "#3366CC")
                self.sources_layout.addWidget(badge)
                sources.append("Wikipedia")
        
        if species_data.get('wiki_url'):
            badge = InfoBadge("Wiki", "#3366CC")
            self.sources_layout.addWidget(badge)
            sources.append("Wikipedia")
        
        if species_data.get('occurrence_stats', {}).get('total_records', 0) > 0:
            badge = InfoBadge("OBIS", SUCCESS_COLOR)
            self.sources_layout.addWidget(badge)
            sources.append("Ocean Biogeographic Information System (OBIS)")
        
        self.sources_layout.addStretch()
        
        # Show sources label if we have sources
        if sources:
            self.sources_label.show()
        else:
            self.sources_label.hide()

    def update_taxonomy_tab(self, species_data):
        """Update taxonomy tab"""
        taxonomy = species_data.get('taxonomy', {})
        
        # Update taxonomy labels
        for rank, label in self.taxonomy_labels.items():
            if rank in taxonomy:
                label.setText(taxonomy[rank])
            else:
                label.setText("—")
        
        # Update notes
        if species_data.get('source') == 'local':
            self.taxonomy_notes.setText("Note: User-added species may not have complete taxonomic data.")
        else:
            self.taxonomy_notes.setText("Taxonomic data from WoRMS (World Register of Marine Species).")

    def update_habitat_tab(self, species_data):
        """Update habitat tab"""
        depth_info = species_data.get('depth_info', {})
        
        # Update depth details
        if depth_info:
            source = depth_info.get('source', 'Unknown source')
            avg_depth = depth_info.get('avg_depth', 0)
            min_depth = depth_info.get('min_depth', 0)
            max_depth = depth_info.get('max_depth', 0)
            
            depth_text = f"• Source: {source}\n"
            depth_text += f"• Average depth: {int(avg_depth):,} m\n"
            depth_text += f"• Range: {int(min_depth):,}–{int(max_depth):,} m\n"
            
            if avg_depth < 200:
                depth_text += "• Zone: Epipelagic (Sunlight Zone, 0-200m)"
            elif avg_depth < 1000:
                depth_text += "• Zone: Mesopelagic (Twilight Zone, 200-1000m)"
            elif avg_depth < 4000:
                depth_text += "• Zone: Bathypelagic (Midnight Zone, 1000-4000m)"
            else:
                depth_text += "• Zone: Abyssopelagic (Abyss, 4000m+)"
            
            self.depth_details.setText(depth_text)
        else:
            self.depth_details.setText("No depth data available.")
        
        # Update environment details
        habitat = species_data.get('habitat', '')
        distribution = species_data.get('distribution', [])
        
        env_text = f"• Habitat: {habitat}\n"
        
        if distribution:
            env_text += f"• Distribution: {', '.join(distribution[:3])}"
            if len(distribution) > 3:
                env_text += f"... (+{len(distribution)-3} more)"
        
        self.environment_details.setText(env_text)

    def update_distribution_tab(self, species_data):
        """Update distribution tab"""
        distribution = species_data.get('distribution', [])
        
        if distribution:
            dist_text = "\n".join([f"• {loc}" for loc in distribution])
            self.distribution_text.setText(dist_text)
            
            # Force top alignment
            self.distribution_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
            
            # Calculate required height based on content using QTextDocument
            dist_width = max(200, self.distribution_text.width() - 24)
            
            # Use QTextDocument for accurate height calculation
            temp_doc = QTextDocument()
            temp_doc.setDefaultFont(self.distribution_text.font())
            temp_doc.setTextWidth(dist_width)
            temp_doc.setPlainText(dist_text)
            
            required_height = int(temp_doc.size().height()) + 16  # Add padding
            
            # Set minimum and maximum limits
            min_height = 60
            max_height = 300
            
            # Ensure height is within reasonable bounds
            calculated_height = max(min_height, min(max_height, required_height))
            
            # Set the calculated height
            self.distribution_text.setFixedHeight(calculated_height)
            
            # Update source label
            source_text = "Data source: "
            sources = []
            if species_data.get('source') == 'worms_obis':
                sources.append("WoRMS")
            if species_data.get('occurrence_stats', {}).get('total_records', 0) > 0:
                sources.append("OBIS")
            if species_data.get('wiki_url'):
                sources.append("Wikipedia")
            
            if sources:
                self.distribution_source_label.setText(f"Data source: {', '.join(sources)}")
            else:
                self.distribution_source_label.setText("Data source: Unknown")
                
        else:
            self.distribution_text.setText("No distribution data available.")
            self.distribution_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
            self.distribution_text.setFixedHeight(60)
            self.distribution_source_label.setText("Data source: None")
        
        # Update distribution text styling with reduced top padding
        distribution_text_style = f"""
            QTextEdit {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 4px 8px 8px 8px;  /* Top padding reduced to 4px */
                font-size: 12px;
                background-color: {'white' if not IS_DARK_MODE else DARK_BG};
                color: {TEXT_COLOR};
                selection-background-color: {SECONDARY_COLOR}40;
                text-align: left;
            }}
            QTextEdit:focus {{
                border: 2px solid {SECONDARY_COLOR};
            }}
        """
        self.distribution_text.setStyleSheet(distribution_text_style)

    def update_occurrence_tab(self, species_data):
        """Update occurrence tab"""
        stats = species_data.get('occurrence_stats', {})
        
        # Update stat labels
        self.occurrence_stats['total_records'].setText(f"{stats.get('total_records', 0):,}")
        self.occurrence_stats['year_range'].setText(stats.get('year_range', '—'))
        
        has_depth = "Yes" if stats.get('has_depth_data') else "No"
        self.occurrence_stats['with_depth_data'].setText(has_depth)
        
        has_coords = "Yes" if stats.get('has_coordinates') else "No"
        self.occurrence_stats['with_coordinates'].setText(has_coords)
        
        # Calculate and display data quality
        quality_score = 0
        if stats.get('total_records', 0) > 0:
            quality_score += 25
        
        if stats.get('has_depth_data'):
            quality_score += 25
        
        if stats.get('has_coordinates'):
            quality_score += 25
        
        if stats.get('year_range'):
            quality_score += 25
        
        self.quality_bar.setValue(quality_score)
        
        if quality_score >= 75:
            quality_text = "High quality data"
            color = SUCCESS_COLOR
        elif quality_score >= 50:
            quality_text = "Moderate quality data"
            color = "#f39c12"
        else:
            quality_text = "Limited data available"
            color = WARNING_COLOR
        
        self.quality_label.setText(quality_text)
        self.quality_label.setStyleSheet(f"color: {color}; font-weight: bold;")

    def update_info_tab(self, species_data):
        """Update info tab with dynamic height adjustment and top alignment"""
        # Update description
        description = species_data.get('extract', 'No description available.')
        self.description_text.setText(description)
        
        # Force top alignment
        self.description_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        
        # Calculate required height for description
        desc_width = max(200, self.description_text.width() - 24)  # Account for padding and borders
        
        if description.strip():
            # Create a temporary text layout to calculate height more accurately
            temp_doc = QTextDocument()
            temp_doc.setDefaultFont(self.description_text.font())
            temp_doc.setTextWidth(desc_width)
            temp_doc.setPlainText(description.strip())
            
            # Calculate height based on document size
            desc_required_height = int(temp_doc.size().height()) + 16  # Add padding
            
            # Set bounds
            desc_min_height = 60
            desc_max_height = 400
            
            desc_calculated_height = max(desc_min_height, min(desc_max_height, desc_required_height))
            self.description_text.setFixedHeight(desc_calculated_height)
        else:
            self.description_text.setFixedHeight(60)
        
        # Update sources text
        sources_text = ""
        
        if species_data.get('source') == 'worms_obis':
            sources_text += "• World Register of Marine Species (WoRMS)\n"
            sources_text += "• Ocean Biogeographic Information System (OBIS)\n"
        
        if species_data.get('wiki_url'):
            sources_text += f"• Wikipedia: {species_data.get('wiki_url')}\n"
        
        if species_data.get('thumb_url') and 'wikipedia' in species_data.get('thumb_url', ''):
            sources_text += "• Wikipedia Commons (images)\n"
        
        if species_data.get('source') == 'local':
            sources_text += "• User-contributed data\n"
        
        if not sources_text:
            sources_text = "No source information available."
        
        self.sources_text.setText(sources_text)
        
        # Force top alignment
        self.sources_text.setAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        
        # Calculate required height for sources
        sources_width = max(200, self.sources_text.width() - 24)  # Account for padding and borders
        
        if sources_text.strip():
            # Use QTextDocument for more accurate height calculation
            temp_doc = QTextDocument()
            temp_doc.setDefaultFont(self.sources_text.font())
            temp_doc.setTextWidth(sources_width)
            temp_doc.setPlainText(sources_text.strip())
            
            sources_required_height = int(temp_doc.size().height()) + 16  # Add padding
            
            # Set bounds
            sources_min_height = 40
            sources_max_height = 200
            
            sources_calculated_height = max(sources_min_height, 
                                          min(sources_max_height, sources_required_height))
            self.sources_text.setFixedHeight(sources_calculated_height)
        else:
            self.sources_text.setFixedHeight(40)
        
        # Apply styles to ensure text is top-aligned with minimal top padding
        desc_style = f"""
            QTextEdit {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 4px 8px 8px 8px;  /* Top padding reduced to 4px */
                font-size: 11px;
                background-color: {'white' if not IS_DARK_MODE else DARK_BG};
                color: {TEXT_COLOR};
                selection-background-color: {SECONDARY_COLOR}40;
                text-align: left;
            }}
            QTextEdit:focus {{
                border: 2px solid {SECONDARY_COLOR};
            }}
        """
        
        self.description_text.setStyleSheet(desc_style)
        
        sources_style = f"""
            QTextEdit {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 4px 8px 8px 8px;  /* Top padding reduced to 4px */
                font-size: 9px;
                background-color: {'white' if not IS_DARK_MODE else DARK_BG};
                color: {TEXT_COLOR};
                selection-background-color: {SECONDARY_COLOR}40;
                text-align: left;
            }}
            QTextEdit:focus {{
                border: 2px solid {SECONDARY_COLOR};
            }}
        """
        
        self.sources_text.setStyleSheet(sources_style)
        
        # Force a layout update to ensure top alignment takes effect
        self.description_text.update()
        self.sources_text.update()

    def apply_theme(self):
        """Apply the current theme to the application"""
        app = QApplication.instance()
        
        # Update theme button text
        if IS_DARK_MODE:
            self.theme_toggle_btn.setText("☀️")
        else:
            self.theme_toggle_btn.setText("🌙")
        
        # Apply stylesheet
        app.setStyleSheet(get_theme_stylesheet())
        
        # Update specific widget styles
        button_style = f"""
            QPushButton {{
                background: {SECONDARY_COLOR};
                color: {'white' if not IS_DARK_MODE else TEXT_COLOR};
                font-weight: bold;
                padding: 10px;
                border-radius: 6px;
                border: 1px solid {SECONDARY_COLOR};
            }}
            QPushButton:hover {{
                background: {SECONDARY_COLOR}dd;
            }}
            QPushButton:pressed {{
                background: {SECONDARY_COLOR}aa;
            }}
        """
        
        accent_button_style = f"""
            QPushButton {{
                background: {ACCENT_COLOR};
                color: white;
                font-weight: bold;
                padding: 10px;
                border-radius: 6px;
                border: 1px solid {ACCENT_COLOR};
            }}
            QPushButton:hover {{
                background: {ACCENT_COLOR}dd;
            }}
            QPushButton:pressed {{
                background: {ACCENT_COLOR}aa;
            }}
        """
        
        warning_button_style = f"""
            QPushButton {{
                background: {WARNING_COLOR};
                color: white;
                font-weight: bold;
                padding: 10px;
                border-radius: 6px;
                border: 1px solid {WARNING_COLOR};
            }}
            QPushButton:hover {{
                background: {WARNING_COLOR}dd;
            }}
            QPushButton:pressed {{
                background: {WARNING_COLOR}aa;
            }}
            QPushButton:disabled {{
                background: {TEXT_SECONDARY};
                color: {LIGHT_BG};
                border: 1px solid {TEXT_SECONDARY};
            }}
        """
        
        # Small square button style for theme toggle
        theme_toggle_style = f"""
            QPushButton {{
                background: {LIGHT_BG};
                color: {TEXT_COLOR};
                font-weight: bold;
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 0px;
                margin: 0px;
            }}
            QPushButton:hover {{
                background: {SECONDARY_COLOR}20;
                border: 1px solid {SECONDARY_COLOR};
            }}
            QPushButton:pressed {{
                background: {SECONDARY_COLOR}40;
            }}
        """
        
        # Apply button styles
        self.search_button.setStyleSheet(button_style)
        self.browse_button.setStyleSheet(button_style)
        self.browse_more_btn.setStyleSheet(button_style)
        self.add_btn.setStyleSheet(button_style)
        self.delete_btn.setStyleSheet(warning_button_style)
        self.add_image_btn.setStyleSheet(accent_button_style)
        self.theme_toggle_btn.setStyleSheet(theme_toggle_style)
        
        # Update loading overlay
        if hasattr(self, 'loading_overlay'):
            self.loading_overlay.update_style()
        
        # Update specific labels
        name_label_style = f"font-size: 24px; font-weight: bold; color: {TEXT_COLOR};"
        self.name_label.setStyleSheet(name_label_style)
        
        aphia_id_style = f"""
            font-family: monospace;
            color: {TEXT_SECONDARY};
            background: {LIGHT_BG};
            padding: 4px 10px;
            border-radius: 4px;
        """
        self.aphia_id_label.setStyleSheet(aphia_id_style)
        
        sci_name_style = f"""
            font-size: 18px;
            font-style: italic;
            color: {PRIMARY_COLOR};
            padding-bottom: 10px;
            border-bottom: 1px solid {BORDER_COLOR};
        """
        self.sci_name_label.setStyleSheet(sci_name_style)
        
        habitat_style = f"color: {TEXT_COLOR}; font-size: 14px;"
        self.habitat_label.setStyleSheet(habitat_style)
        
        sources_label_style = f"color: {TEXT_SECONDARY}; font-size: 12px; margin-top: 10px;"
        self.sources_label.setStyleSheet(sources_label_style)
        
        results_count_style = f"color: {TEXT_SECONDARY}; font-size: 11px; padding: 2px;"
        self.results_count.setStyleSheet(results_count_style)
        
        image_label_style = f"color: {TEXT_SECONDARY}; font-size: 14px;"
        self.image_label.setStyleSheet(image_label_style)
        
        image_source_style = f"color: {TEXT_SECONDARY}; font-size: 10px;"
        self.image_source.setStyleSheet(image_source_style)
        
        # Update image frame
        image_frame_style = f"""
            QFrame#imageFrame {{
                border-radius: 8px;
                background: {LIGHT_BG};
                min-width: 320px;
                min-height: 240px;
                max-width: 400px;
                max-height: 300px;
            }}
        """
        self.image_frame.setStyleSheet(image_frame_style)
        
        # Update list widget
        list_style = f"""
            QListWidget#speciesList {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                background: {'white' if not IS_DARK_MODE else DARK_BG};
                outline: none;
                padding: 0px;
                margin: 0px;
            }}
            QListWidget#speciesList::item {{
                border: none;
                padding: 0px;
                margin: 0px;
                background: transparent;
                outline: none;
            }}
            QListWidget#speciesList::item:selected {{
                background: transparent;
                border: none;
                outline: none;
            }}
            QListWidget#speciesList::item:hover {{
                background: transparent;
                outline: none;
            }}
            QScrollBar:vertical {{
                border: none;
                background: {LIGHT_BG};
                width: 14px;
                margin: 0px;
                border-top-right-radius: 4px;
                border-bottom-right-radius: 4px;
            }}
            QScrollBar::handle:vertical {{
                background: {BORDER_COLOR};
                border-radius: 0px;
                min-height: 30px;
                margin: 0px;
                border-top-right-radius: 4px;
                border-bottom-right-radius: 4px;
            }}
            QScrollBar::handle:vertical:hover {{
                background: {TEXT_SECONDARY};
            }}
            QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {{
                border: none;
                background: none;
                height: 0px;
            }}
            QScrollBar:horizontal {{
                height: 0px;
            }}
        """
        self.list_widget.setStyleSheet(list_style)
        
        # Update group boxes
        group_box_style = f"""
            QGroupBox {{
                font-weight: bold;
                border: 2px solid {BORDER_COLOR};
                border-radius: 6px;
                margin-top: 10px;
                padding-top: 10px;
                margin: 2px;
                background-color: {'white' if not IS_DARK_MODE else DARK_BG};
                color: {TEXT_COLOR};
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
                color: {TEXT_COLOR};
            }}
        """
        
        # Update text edit widgets with reduced top padding
        text_edit_style = f"""
            QTextEdit {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                padding: 4px 8px 8px 8px;  /* Top padding reduced to 4px */
                font-size: 11px;
                background-color: {'white' if not IS_DARK_MODE else DARK_BG};
                color: {TEXT_COLOR};
                text-align: left;
            }}
        """
        
        self.distribution_text.setStyleSheet(text_edit_style)
        self.description_text.setStyleSheet(text_edit_style)
        self.sources_text.setStyleSheet(text_edit_style.replace('11px', '9px'))
        
        # Update progress bar
        progress_bar_style = f"""
            QProgressBar {{
                border: 1px solid {BORDER_COLOR};
                border-radius: 4px;
                background: {LIGHT_BG};
            }}
            QProgressBar::chunk {{
                background: {ACCENT_COLOR};
                border-radius: 4px;
            }}
        """
        self.quality_bar.setStyleSheet(progress_bar_style)
        
        # Update taxonomy notes
        taxonomy_notes_style = f"""
            color: {TEXT_COLOR};
            font-size: 10px;
            padding: 6px;
            background: {LIGHT_BG};
            border-radius: 4px;
        """
        self.taxonomy_notes.setStyleSheet(taxonomy_notes_style)
        
        # Update quality label
        quality_label_style = f"color: {TEXT_COLOR}; font-size: 10px;"
        self.quality_label.setStyleSheet(quality_label_style)
        
        # Update taxonomy labels
        taxonomy_label_style = f"color: {TEXT_COLOR}; padding: 2px; font-size: 12px;"
        for label in self.taxonomy_labels.values():
            label.setStyleSheet(taxonomy_label_style)
        
        # Update occurrence stats labels
        occurrence_stat_style = f"color: {TEXT_COLOR}; padding: 2px; font-size: 12px;"
        for label in self.occurrence_stats.values():
            label.setStyleSheet(occurrence_stat_style)
        
        # Update depth and environment details
        details_style = f"color: {TEXT_COLOR}; padding: 4px; font-size: 12px;"
        self.depth_details.setStyleSheet(details_style)
        self.environment_details.setStyleSheet(details_style)
        
        # Refresh all widgets
        self.update()
        
    def toggle_theme(self):
        """Toggle between light and dark mode"""
        toggle_dark_mode()
        self.apply_theme()
        
        # Explicitly update the loading overlay
        if hasattr(self, 'loading_overlay'):
            self.loading_overlay.update_style()
        
        # Refresh the current species display to update colors
        if self.current_species_data:
            self.display_species_details(self.current_species_data)

def main():
    """Main entry point"""
    print(">>> DEBUG: Starting MarineScope...")
    print(">>> DEBUG: Data sources: WoRMS + OBIS v3 + Wikipedia")

    # Start application
    app = QApplication(sys.argv)
    
    # Set application style
    app.setStyle("Fusion")

    # Set application palette for better doodle visibility
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#fffef7"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#2c3e50"))
    palette.setColor(QPalette.ColorRole.Base, QColor("#ffffff"))
    app.setPalette(palette)
    
    # Show startup screen
    splash = StartupScreen()
    splash.show()
    # Get screen size and set splash to 80% of screen
    screen_geometry = app.primaryScreen().availableGeometry()
    splash_width = int(screen_geometry.width() * 1)
    splash_height = int(screen_geometry.height() * 1)
    splash.resize(splash_width, splash_height)

    # Center it
    splash.move(
        (screen_geometry.width() - splash.width()) // 2,
        (screen_geometry.height() - splash.height()) // 2
    )
    
    # Update loading status
    splash.update_progress(10, "Initializing application...")
    
    splash.update_progress(20, "Checking local storage...")
    
    # Ensure user_species.json exists
    script_dir = os.path.dirname(os.path.abspath(__file__))
    user_species_path = os.path.join(script_dir, USER_SPECIES_FILE)
    
    if not os.path.exists(user_species_path):
        with open(user_species_path, "w", encoding="utf-8") as f:
            json.dump([], f, ensure_ascii=False, indent=2)
        print(f">>> DEBUG: Created {user_species_path}")
    
    # Create user_images directory
    user_images_dir = os.path.join(script_dir, 'user_images')
    os.makedirs(user_images_dir, exist_ok=True)
    
    splash.update_progress(40, "Loading marine database...")
    
    # Initialize high-level taxa
    print(">>> DEBUG: Loading high-level marine animals from WoRMS...")
    initialize_high_level_taxa()
    print(f">>> DEBUG: Loaded {len(HIGH_LEVEL_TAXA)} high-level marine animal groups")
    
    splash.update_progress(60, "Testing API connections...")
    
    # Test WoRMS API with better debugging
    print(">>> Testing WoRMS API...")
    test_worms_api()
    
    splash.update_progress(75, "Creating main window...")
    
    # Create main window
    window = MainWindow()
    
    # Set window size
    screen = app.primaryScreen()
    screen_geometry = screen.availableGeometry()
    window.resize(int(screen_geometry.width() * 0.9), int(screen_geometry.height() * 0.85))
    
    splash.update_progress(100, "Ready!")
    QApplication.processEvents()
    
    # Close splash and show main window
    splash.finish(window)
    window.show()
    
    print(">>> DEBUG: Application started successfully")
    print(">>> DEBUG: Features: WoRMS taxonomy + OBIS v3 data + Wikipedia + User species")
    print(">>> DEBUG: Focus: Marine animals (fish, mammals, reptiles, cephalopods)")
    
    sys.exit(app.exec())

if __name__ == '__main__':
    main()