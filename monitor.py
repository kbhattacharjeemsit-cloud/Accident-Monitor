#!/usr/bin/env python3
"""
India Accident News Monitor  (v6 - full rewrite)
================================================

WHY THIS WAS REWRITTEN
----------------------
Versions 1-5 filtered by BLOCKLIST: keep everything, then remove what is known
to be bad. That fails permanently, because anything not yet thought of gets
through - Bangladeshi outlets, Alaskan crashes, food-safety stories, trekking
deaths, protest blockades, murders, 1984 riot retrospectives.

v6 inverts the logic. NOTHING is kept unless it PROVES all four gates:

    GATE 1  SOURCE   - published by a recognised Indian outlet
                       (or, for an unknown outlet, the text proves it is Indian)
    GATE 2  INDIA    - names an Indian place/state, or India itself
    GATE 3  ACCIDENT - an UNINTENTIONAL physical incident: crash, collapse,
                       derailment, capsize, industrial mishap.
                       NOT violence, illness, food safety, sport, adventure,
                       protest, policy or crime.
    GATE 4  CURRENT  - happened now, not years ago, and is a report of the
                       event itself rather than an investigation, statistic,
                       commemoration or aftermath.

Failing any gate drops the item, and the reason is counted in the run log, so
exclusions are visible rather than silent.

Standard library only. No pip install. No API keys. No paid services.
"""

import base64
import csv
import hashlib
import html
import json
import re
import sqlite3
import sys
import time
import urllib.parse
import urllib.request
from collections import OrderedDict
from datetime import datetime, timezone
from difflib import SequenceMatcher
from email.utils import parsedate_to_datetime
from xml.etree import ElementTree

# ===========================================================================
# CONFIG
# ===========================================================================
MIN_DATE = "2026-06-01"
EVENT_DATE_WINDOW_DAYS = 3
EVENT_SIM_THRESHOLD = 0.70
TITLE_DUP_THRESHOLD = 0.90
TRANSLATE_BACKEND = "builtin"      # "builtin" | "none"
MAX_TRANSLATE_PER_RUN = 4000
MAX_ARTICLE_FETCH_PER_RUN = 1200
FETCH_TIMEOUT = 12
DB_PATH = "accidents.db"
UA = "Mozilla/5.0 (compatible; AccidentMonitor/6.0)"

EDITIONS = {
    "en": ("English", "IN:en"), "hi": ("Hindi", "IN:hi"), "bn": ("Bengali", "IN:bn"),
    "mr": ("Marathi", "IN:mr"), "ta": ("Tamil", "IN:ta"), "te": ("Telugu", "IN:te"),
    "kn": ("Kannada", "IN:kn"), "ml": ("Malayalam", "IN:ml"), "gu": ("Gujarati", "IN:gu"),
    "pa": ("Punjabi", "IN:pa"),
}

GN_QUERIES = {
    "en": ['road accident India killed', 'bus truck accident India',
           'train accident India derailment', 'building collapse India',
           'bridge flyover collapse India', 'factory accident India workers',
           'plane crash India airport', 'boat capsize India'],
    "hi": ['सड़क हादसा मौत', 'बस ट्रक दुर्घटना', 'ट्रेन हादसा', 'इमारत ढही', 'पुल गिरा', 'फैक्ट्री हादसा'],
    "bn": ['সড়ক দুর্ঘটনা নিহত', 'বাস ট্রাক দুর্ঘটনা', 'ট্রেন দুর্ঘটনা', 'ভবন ধস', 'কারখানা দুর্ঘটনা'],
    "mr": ['रस्ता अपघात मृत्यू', 'बस अपघात', 'रेल्वे अपघात', 'इमारत कोसळली', 'कारखाना अपघात'],
    "ta": ['சாலை விபத்து உயிரிழப்பு', 'பேருந்து விபத்து', 'ரயில் விபத்து', 'கட்டிடம் இடிந்து'],
    "te": ['రోడ్డు ప్రమాదం మృతి', 'బస్సు ప్రమాదం', 'రైలు ప్రమాదం', 'భవనం కూలింది'],
    "kn": ['ರಸ್ತೆ ಅಪಘಾತ ಸಾವು', 'ಬಸ್ ಅಪಘಾತ', 'ರೈಲು ಅಪಘಾತ', 'ಕಟ್ಟಡ ಕುಸಿತ'],
    "ml": ['റോഡ് അപകടം മരണം', 'ബസ് അപകടം', 'ട്രെയിൻ അപകടം', 'കെട്ടിടം തകർന്നു'],
    "gu": ['માર્ગ અકસ્માત મોત', 'બસ અકસ્માત', 'ટ્રેન અકસ્માત', 'ઇમારત ધરાશાયી'],
    "pa": ['ਸੜਕ ਹਾਦਸਾ ਮੌਤ', 'ਬੱਸ ਹਾਦਸਾ', 'ਰੇਲ ਹਾਦਸਾ', 'ਇਮਾਰਤ ਢਹਿ'],
}

NEWSPAPER_FEEDS = [
    ("English", "https://indianexpress.com/feed/"),
    ("English", "https://www.thehindu.com/news/national/feeder/default.rss"),
    ("English", "https://feeds.feedburner.com/ndtvnews-india-news"),
    ("English", "https://www.news18.com/rss/india.xml"),
    ("Hindi",   "https://feed.livehindustan.com/rss/3127"),
]

RSS_SEARCH = "https://news.google.com/rss/search?q="

# ===========================================================================
# GATE 1 - SOURCE
# ===========================================================================
INDIAN_SOURCES = {
    "times of india", "timesofindia", "hindustan times", "hindustantimes", "the hindu", "thehindu",
    "indian express", "indianexpress", "ndtv", "news18", "india today", "indiatoday", "firstpost",
    "the print", "theprint", "the wire", "thewire", "scroll.in", "deccan herald", "deccanherald",
    "deccan chronicle", "deccanchronicle", "telegraph india", "telegraphindia", "business standard",
    "businessstandard", "economic times", "economictimes", "livemint", "financial express",
    "financialexpress", "the tribune", "tribuneindia", "the statesman", "thestatesman", "mid-day",
    "midday", "dna india", "dnaindia", "outlook", "the quint", "thequint", "moneycontrol",
    "zee news", "zeenews", "abp live", "abplive", "republic", "wion", "cnbc tv18", "cnbctv18",
    "india tv", "indiatv", "aaj tak", "aajtak", "tv9", "etv bharat", "etvbharat", "asianet",
    "manorama", "mathrubhumi", "new indian express", "newindianexpress", "the week", "theweek",
    "press trust of india", "uni india", "opindia", "oneindia", "jansatta", "amar bharati",
    "dainik bhaskar", "bhaskar", "jagran", "amar ujala", "amarujala", "navbharat times",
    "navbharattimes", "hindustan", "livehindustan", "patrika", "prabhat khabar", "prabhatkhabar",
    "nai dunia", "naidunia", "punjab kesari", "punjabkesari", "lokmat", "haribhoomi", "news24",
    "rajasthan patrika", "dainik jagran", "swadesh", "india.com", "abplive",
    "anandabazar", "ei samay", "eisamay", "bartaman", "sangbad pratidin", "sangbadpratidin",
    "aajkaal", "uttarbanga", "abp ananda", "24 ghanta", "zee 24", "hindustan times bangla",
    "loksatta", "maharashtra times", "maharashtratimes", "sakal", "esakal", "pudhari",
    "abp majha", "saamana", "divya marathi", "webdunia", "policenama", "lokmat times",
    "dinamalar", "dinamani", "daily thanthi", "dailythanthi", "dinakaran", "maalaimalar",
    "hindu tamil", "vikatan", "puthiyathalaimurai", "polimer", "news7 tamil",
    "eenadu", "sakshi", "andhrajyothy", "namasthe telangana", "ntv telugu", "abn andhra",
    "v6 velugu", "hmtv", "10tv", "disha daily", "lokal", "prabha news", "great andhra",
    "vijaya karnataka", "vijayakarnataka", "prajavani", "udayavani", "kannada prabha",
    "public tv", "suvarna news", "news18 kannada",
    "manorama online", "madhyamam", "deshabhimani", "kerala kaumudi", "twentyfour",
    "reporter live", "asianet news", "samakalika malayalam", "marunadan",
    "sandesh", "gujarat samachar", "gujaratsamachar", "divya bhaskar", "divyabhaskar",
    "abp asmita", "nobat", "gujarati",
    "ajit", "jagbani", "punjabi jagran", "punjabi tribune", "abp sanjha", "ptc news",
    "rozana spokesman", "babushahi",
    "orissapost", "sambad", "dharitri", "odishatv", "kanak news", "assam tribune",
    "pratidin time", "sentinelassam", "nagaland post", "shillong times", "greater kashmir",
    "rising kashmir", "daily excelsior", "kashmir reader", "herald goa", "navhind",
    "kolkata24x7", "kolkata tv", "calcutta news", "najarbandi", "ganashakti",
    "uttarbanga sambad", "news18 bangla", "focus bangla", "khabor", "sanbad",
}

FOREIGN_SOURCES = {
    # Bangladesh
    "prothom alo", "prothomalo", "daily star", "thedailystar", "bdnews24", "kalerkantho",
    "jugantor", "ittefaq", "samakal", "bangla tribune", "banglatribune", "ajkalerkhobor",
    "banglanews", "risingbd", "bd-pratidin", "bdpratidin", "dhaka post", "dhakapost",
    "dhaka mail", "dhaka tribune", "dhakatribune", "naya diganta", "nayadiganta",
    "ajker patrika", "desh rupantor", "jagonews", "somoy news", "channel24", "jamuna tv",
    "ntv bd", "bangladesh pratidin", "manabzamin", "amader shomoy", "bhorer kagoj",
    "observerbd", "newagebd", "tbsnews", "businesspostbd", "bd24live", "bd24report",
    "bd-journal", "bdjournal", "dhakaprokash", "citynewsdhaka", "protidinerbangladesh",
    "bangladeshtimes", "the new nation", "daily bangla post", "bangladesh sangbad",
    "sarabangla", "barta24", "dailyinqilab", "amardesh", "shomoyeralo", "banglavision",
    "independent bd", "banglar janarob",
    ".bd/", "bangladesh",
    # Pakistan / Nepal / Sri Lanka
    "dawn.com", "geo news", "geo tv", "ary news", "express tribune", "the news international",
    "samaa", "dunya news", "nawaiwaqt", "bol news", "pakistan today", "pakistan observer",
    "kathmandu post", "himalayan times", "onlinekhabar", "ekantipur", "setopati", "myrepublica",
    "ada derana", "colombo page", "daily mirror sri", "newsfirst.lk", "sundaytimes.lk",
    "dailynews.lk", "lankadeepa",
    # elsewhere
    "vietnam.vn", "vnexpress", "xinhua", "global times", "china daily",
    "bbc", "al jazeera", "aljazeera", "cnn", "sputnik", "voanews", "dw.com", "deutsche welle",
    "reuters", "associated press", "ap news", "afp", "the guardian", "new york times",
    "nytimes", "washington post", "fox news", "sky news", "abc news", "cbs news", "nbc news",
    "usa today", "daily mail", "the sun", "mirror.co.uk",
}


def source_verdict(source, url=""):
    """'indian' | 'foreign' | 'unknown'.

    Note on a mistake worth not repeating: "Kolkata24x7" and "najarbandi.in" were
    briefly blocked here because "24" and "bangla" resemble Bangladeshi outlet
    names. Both are West Bengal publications. Bengali-language does NOT mean
    Bangladeshi, and matching must be on the outlet, not on the language.
    """
    hay = ((source or "") + " " + (url or "")).lower()
    # an Indian domain settles it
    if re.search(r"\.in\b|\.co\.in\b|india\.com", hay):
        return "indian"
    for f in FOREIGN_SOURCES:
        if f in hay:
            return "foreign"
    for i in INDIAN_SOURCES:
        if i in hay:
            return "indian"
    return "unknown"


# ===========================================================================
# GATE 2 - INDIA
# ===========================================================================
STATES = ["Andhra Pradesh", "Arunachal Pradesh", "Assam", "Bihar", "Chhattisgarh", "Goa",
    "Gujarat", "Haryana", "Himachal Pradesh", "Jharkhand", "Karnataka", "Kerala",
    "Madhya Pradesh", "Maharashtra", "Manipur", "Meghalaya", "Mizoram", "Nagaland", "Odisha",
    "Punjab", "Rajasthan", "Sikkim", "Tamil Nadu", "Telangana", "Tripura", "Uttar Pradesh",
    "Uttarakhand", "West Bengal", "Delhi", "Jammu and Kashmir", "Ladakh", "Puducherry",
    "Chandigarh"]

CITIES = ["Mumbai", "New Delhi", "Kolkata", "Chennai", "Bengaluru", "Bangalore", "Hyderabad",
    "Ahmedabad", "Pune", "Jaipur", "Lucknow", "Kanpur", "Nagpur", "Patna", "Bhopal", "Indore",
    "Thane", "Visakhapatnam", "Vadodara", "Ghaziabad", "Ludhiana", "Agra", "Nashik", "Faridabad",
    "Meerut", "Rajkot", "Varanasi", "Srinagar", "Aurangabad", "Dhanbad", "Amritsar", "Prayagraj",
    "Allahabad", "Ranchi", "Howrah", "Coimbatore", "Jabalpur", "Gwalior", "Vijayawada", "Jodhpur",
    "Madurai", "Raipur", "Kota", "Guwahati", "Thiruvananthapuram", "Solapur", "Hubballi",
    "Bareilly", "Mysuru", "Mysore", "Gurugram", "Gurgaon", "Noida", "Aligarh", "Jalandhar",
    "Bhubaneswar", "Salem", "Warangal", "Guntur", "Saharanpur", "Gorakhpur", "Bikaner", "Amravati",
    "Jamshedpur", "Bhilai", "Cuttack", "Kochi", "Nellore", "Bhavnagar", "Dehradun", "Durgapur",
    "Asansol", "Rourkela", "Nanded", "Kolhapur", "Ajmer", "Jamnagar", "Ujjain", "Siliguri",
    "Jhansi", "Mangaluru", "Mangalore", "Erode", "Belagavi", "Tirupati", "Udaipur", "Panaji",
    "Shillong", "Imphal", "Aizawl", "Kohima", "Itanagar", "Gangtok", "Agartala", "Shimla",
    "Vellore", "Tiruchirappalli", "Trichy", "Tirunelveli", "Tiruppur", "Kozhikode", "Thrissur",
    "Kollam", "Kannur", "Muzaffarpur", "Gaya", "Bhagalpur", "Darbhanga", "Rohtak", "Panipat",
    "Karnal", "Ambala", "Hisar", "Sonipat", "Moradabad", "Junagadh", "Anand", "Surat",
    "Navi Mumbai", "Kalyan", "Sangli", "Latur", "Akola", "Ratlam", "Sagar", "Satna", "Rewa",
    "Bilaspur", "Korba", "Sambalpur", "Berhampur", "Puri", "Dibrugarh", "Silchar", "Tezpur",
    "Jorhat", "Nagaon", "Bhiwandi", "Palghar", "Chandrapur", "Jalgaon", "Ahmednagar",
    "Muzaffarnagar", "Firozabad", "Mathura", "Ayodhya", "Jaunpur", "Azamgarh", "Ballia",
    "Deoria", "Basti", "Gonda", "Bahraich", "Mirzapur", "Etah", "Hathras", "Hapur", "Rampur",
    "Pilibhit", "Sitapur", "Hardoi", "Unnao", "Raebareli", "Fatehpur", "Banda", "Etawah",
    "Sultanpur", "Pratapgarh", "Ghazipur", "Chandauli", "Bhadohi", "Kushinagar", "Amroha",
    "Sambhal", "Bijnor", "Bulandshahr", "Shahjahanpur", "Lakhimpur", "Barabanki", "Auraiya",
    "Arrah", "Buxar", "Chhapra", "Siwan", "Motihari", "Sitamarhi", "Madhubani", "Samastipur",
    "Begusarai", "Khagaria", "Munger", "Nawada", "Nalanda", "Katihar", "Purnia", "Araria",
    "Saharsa", "Banka", "Jhalawar", "Bokaro", "Deoghar", "Hazaribagh", "Giridih", "Ramgarh",
    "Chaibasa", "Dumka", "Palamu", "Malda", "Barasat", "Jalpaiguri", "Bankura", "Purulia",
    "Kharagpur", "Haldia", "Raiganj", "Arambagh", "Bhilwara", "Alwar", "Sikar", "Pali",
    "Barmer", "Nagaur", "Churu", "Jhunjhunu", "Bharatpur", "Karauli", "Bundi", "Baran",
    "Chittorgarh", "Banswara", "Dungarpur", "Morena", "Bhind", "Shivpuri", "Guna", "Vidisha",
    "Sehore", "Betul", "Chhindwara", "Seoni", "Balaghat", "Katni", "Damoh", "Chhatarpur",
    "Dewas", "Khandwa", "Khargone", "Dhar", "Durg", "Rajnandgaon", "Jagdalpur", "Raigarh",
    "Balasore", "Bhadrak", "Jajpur", "Angul", "Keonjhar", "Baripada", "Sundargarh", "Bolangir",
    "Koraput", "Rayagada", "Anantnag", "Baramulla", "Udhampur", "Kathua", "Rajouri", "Poonch",
    "Doda", "Leh", "Kargil", "Jammu", "Solan", "Mandi", "Kullu", "Kangra", "Dharamshala",
    "Una", "Hamirpur", "Chamba", "Sirmaur", "Haridwar", "Rishikesh", "Roorkee", "Haldwani",
    "Rudrapur", "Nainital", "Almora", "Pithoragarh", "Chamoli", "Uttarkashi", "Tehri", "Pauri",
    "Bathinda", "Patiala", "Mohali", "Pathankot", "Hoshiarpur", "Moga", "Firozpur", "Faridkot",
    "Muktsar", "Barnala", "Sangrur", "Kapurthala", "Gurdaspur", "Batala", "Khanna", "Phagwara",
    "Rewari", "Bhiwani", "Jind", "Kaithal", "Kurukshetra", "Yamunanagar", "Sirsa", "Palwal",
    "Bharuch", "Vapi", "Valsad", "Navsari", "Mehsana", "Patan", "Godhra", "Nadiad", "Bhuj",
    "Morbi", "Surendranagar", "Amreli", "Porbandar", "Veraval", "Dahod", "Gandhinagar",
    "Tinsukia", "Sivasagar", "Golaghat", "Bongaigaon", "Barpeta", "Dhubri", "Diphu",
    "Sivakasi", "Karur", "Thanjavur", "Dindigul", "Cuddalore", "Nagercoil", "Thoothukudi",
    "Palakkad", "Alappuzha", "Kottayam", "Malappuram", "Wayanad", "Ernakulam", "Kasaragod",
    "Ballari", "Davanagere", "Shivamogga", "Tumakuru", "Raichur", "Bidar", "Hassan", "Udupi",
    "Kurnool", "Kadapa", "Anantapur", "Rajahmundry", "Kakinada", "Eluru", "Ongole", "Chittoor",
    "Karimnagar", "Khammam", "Nizamabad", "Mahbubnagar", "Adilabad", "Sangareddy", "Medak",
    "Nalgonda", "Suryapet", "Dombivli", "Ulhasnagar", "Mumbra", "Panvel", "Vasai", "Wardha",
    "Parbhani", "Beed", "Osmanabad", "Yavatmal", "Buldhana", "Gondia", "Bhandara", "Jalna"]

PLACE_LIST = sorted(set(CITIES + STATES), key=len, reverse=True)
_PLACE_PATTERNS = [(p, re.compile(r"\b" + re.escape(p) + r"\b", re.I)) for p in PLACE_LIST]

# Words that place the EVENT in India. Note what is NOT here: the bare adjective
# "Indian". "Indian-origin pilot killed in US helicopter crash" describes a
# person's origin, not where the crash happened, and treating it as proof of
# location let dozens of foreign crashes through.
INDIA_WORDS = re.compile(
    r"\bin india\b|\bacross india\b|\bindia'?s\b|"
    r"\b(?:bharat|nh[-\s]?\d{1,3}|national highway|state highway|expressway|"
    r"indian railways|irctc|dgca|morth|nhai|vande bharat|rajdhani|shatabdi)\b", re.I)

# Adjectives describing PEOPLE, which say nothing about where an event occurred.
PERSON_ORIGIN = re.compile(r"\b(?:indian[-\s]origin|indian student|indian couple|"
                           r"indian national|indian citizen|indian tourist|malayali|"
                           r"indian[-\s]american|nri)\b", re.I)
INDIA_NATIVE = ["भारत", "ভারত", "இந்தியா", "భారత", "ಭಾರತ", "ഇന്ത്യ", "ભારત", "ਭਾਰਤ"]

FOREIGN_PLACES = re.compile(
    r"\b(?:bangladesh|dhaka|chattogram|chittagong|sylhet|khulna|rajshahi|barisal|rangpur|"
    r"mymensingh|feni|comilla|cumilla|narayanganj|gazipur|bogura|jessore|jashore|tangail|"
    r"noakhali|brahmanbaria|dinajpur|pabna|kushtia|faridpur|sitakunda|"
    r"pakistan|lahore|karachi|islamabad|rawalpindi|peshawar|quetta|multan|faisalabad|"
    r"nepal|kathmandu|pokhara|sri lanka|colombo|kandy|galle|jaffna|mavatthagama|kurunegala|"
    r"afghanistan|kabul|myanmar|yangon|bhutan|maldives|china|beijing|shanghai|vietnam|"
    r"thailand|bangkok|indonesia|jakarta|malaysia|singapore|philippines|manila|japan|tokyo|"
    r"korea|seoul|russia|moscow|ukraine|kyiv|turkey|iran|tehran|iraq|baghdad|syria|israel|"
    r"gaza|palestine|egypt|cairo|saudi|riyadh|jeddah|mecca|medina|dubai|abu dhabi|qatar|doha|"
    r"kuwait|oman|muscat|bahrain|yemen|nigeria|lagos|kenya|nairobi|ethiopia|addis ababa|"
    r"congo|ghana|tanzania|uganda|south africa|johannesburg|morocco|algeria|tunisia|libya|"
    r"brazil|sao paulo|mexico|peru|lima|bolivia|colombia|bogota|argentina|chile|venezuela|"
    r"united states|u\.s\.|usa|america|american|alaska|texas|california|florida|new york|"
    r"chicago|washington|canada|toronto|united kingdom|britain|british|england|london|"
    r"scotland|ireland|france|paris|germany|berlin|italy|rome|spain|madrid|portugal|poland|"
    r"warsaw|greece|athens|hungary|budapest|austria|vienna|switzerland|netherlands|belgium|"
    r"sweden|norway|denmark|finland|australia|sydney|melbourne|new zealand|auckland|"
    r"kazakhstan|uzbekistan|azerbaijan|cambodia|laos|taiwan|hong kong|malta|cyprus|serbia|"
    r"croatia|bahamas|africa|europe|middle east|"
    r"\bu\.?k\.?\b|\bus\b|\busa\b|wales|welsh|essex|surrey|kent|yorkshire|manchester|"
    r"birmingham|glasgow|edinburgh|dublin|pennsylvania|ohio|michigan|arizona|nevada|"
    r"colorado|oregon|utah|kansas|iowa|missouri|virginia|carolina|georgia usa|"
    r"dominica|dominican republic|jamaica|cuba|haiti|panama|guatemala|honduras|"
    r"turkiye|azerbaijan|belarus|romania|bulgaria|slovakia|slovenia|estonia|latvia|"
    r"lithuania|iceland|luxembourg|monaco|qatar airways|emirates)\b", re.I)


def india_verdict(text):
    if not text:
        return "unknown"
    if FOREIGN_PLACES.search(text):
        return "foreign"
    # A person's Indian origin is not evidence of an Indian location. If that is
    # the ONLY Indian signal present, the location remains unproven.
    stripped = PERSON_ORIGIN.sub(" ", text)
    if INDIA_WORDS.search(stripped):
        return "india"
    for name, pat in _PLACE_PATTERNS:
        if pat.search(stripped):
            return "india"
    if any(w in stripped for w in INDIA_NATIVE):
        return "india"
    return "unknown"


# ===========================================================================
# GATE 3 - IS IT AN ACCIDENT?
# ===========================================================================
ACCIDENT_EVENT = re.compile(
    r"\b(?:accident|mishap|crash(?:e[sd])?|collision|collide[sd]?|colliding|"
    r"overturn(?:s|ed|ing)?|capsiz(?:e|es|ed|ing)|derail(?:s|ed|ment)?|"
    r"collaps(?:e|es|ed|ing)|caved? in|gave way|razed|"
    r"ran over|run over|mow(?:ed|n) down|knocked down|rammed|skidded|veered|"
    r"plunged|fell into|fell from|toppled|"
    r"blast|explosion|exploded|boiler burst|tyre burst|"
    r"electrocut(?:ed|ion)|asphyxiat\w*|suffocat\w*|"
    r"trapped under|buried under|crushed under|"
    r"fire broke out|caught fire|gutted|"
    r"emergency landing|crash landing|runway excursion|hit and run|head-on)\b", re.I)

ACCIDENT_NATIVE = ["दुर्घटना", "हादसा", "टक्कर", "पलटी", "ढह", "धमाका", "विस्फोट", "आग लग",
    "দুর্ঘটনা", "ধস", "সংঘর্ষ", "উল্টে", "বিস্ফোরণ", "আগুন", "অগ্নিকাণ্ড",
    "अपघात", "कोसळ", "स्फोट", "விபத்து", "மோதி", "இடிந்து", "வெடிப்பு",
    "ప్రమాదం", "ఢీ", "కూలి", "పేలుడు", "ಅಪಘಾತ", "ಕುಸಿತ", "ಸ್ಫೋಟ",
    "അപകടം", "തകർ", "സ്ഫോടനം", "અકસ્માત", "ધરાશાયી", "વિસ્ફોટ",
    "ਹਾਦਸਾ", "ਟੱਕਰ", "ਢਹਿ", "ਧਮਾਕਾ"]

NOT_ACCIDENT = re.compile(
    r"\b(?:murder\w*|killing spree|assault\w*|attack(?:ed|er)?|stabb(?:ed|ing)|"
    r"shot dead|shooting|firing|gunfire|encounter|lynch\w*|beaten to death|"
    r"honour killing|dowry death|rape|molest\w*|abduct\w*|kidnap\w*|hostage|"
    r"riot\w*|communal|mob |clash(?:es|ed)?|violence|arson|terror\w*|militant|naxal|maoist|"
    r"grenade|suicide bomb|"
    r"suicide|self-immolation|ended (?:his|her) life|hanged (?:him|her)self|"
    r"food poison\w*|fungus|expired food|stale food|adulterat\w*|contaminat\w*|"
    r"disease|infection|virus|outbreak|epidemic|dengue|malaria|cholera|"
    r"heart attack|cardiac arrest|heatstroke|heat stroke|snakebite|snake bite|"
    r"malnutrition|starvation|overdose|"
    r"trek(?:king|kers?)?|mountaineer\w*|climbing expedition|paraglid\w*|"
    r"bungee|rafting|scuba|adventure sport|marathon|cricket|football|kabaddi|tournament|"
    r"protest\w*|rally|dharna|strike|bandh|blockade|road block|gherao|agitation|"
    r"morcha|demonstration|sit-in|"
    r"tiger|leopard|elephant attack|wild animal|man-eater|"
    r"fir registered|case registered|arrest(?:ed)?|charge ?sheet|court|bail|verdict|"
    r"compensation|ex-?gratia|solatium|relief fund|"
    r"tribute|homage|mourn\w*|condolence|anniversary|memorial|black day|candle march)\b", re.I)

NOT_ACCIDENT_NATIVE = ["हत्या", "मर्डर", "दंगा", "हमला", "आत्महत्या", "गोली", "बलात्कार", "अपहरण",
    "प्रदर्शन", "धरना", "हड़ताल", "श्रद्धांजलि", "पुण्यतिथि", "ट्रेकिंग",
    "খুন", "হত্যা", "দাঙ্গা", "হামলা", "আত্মহত্যা", "প্রতিবাদ", "শ্রদ্ধাঞ্জলি",
    "आंदोलन", "கொலை", "தாக்குதல்", "தற்கொலை", "போராட்டம்",
    "హత్య", "దాడి", "ఆత్మహత్య", "నిరసన", "ಕೊಲೆ", "ದಾಳಿ", "ಆತ್ಮಹತ್ಯೆ", "ಪ್ರತಿಭಟನೆ",
    "കൊലപാതകം", "ആക്രമണം", "ആത്മഹത്യ", "പ്രതിഷേധം",
    "હત્યા", "હુમલો", "આત્મહત્યા", "વિરોધ", "ਕਤਲ", "ਹਮਲਾ", "ਖ਼ੁਦਕੁਸ਼ੀ", "ਪ੍ਰਦਰਸ਼ਨ"]

NATURAL_HAZARD = re.compile(
    r"\b(?:flood\w*|deluge|inundat\w*|landslide|landslip|mudslide|cloudburst|avalanche|"
    r"earthquake|quake|tremor|cyclone|hurricane|typhoon|tornado|tsunami|lightning|"
    r"thunderbolt|hailstorm|wildfire|forest fire|glacier burst|glacial lake)\b", re.I)
NATURAL_NATIVE = ["बाढ़", "भूस्खलन", "भूकंप", "चक्रवात", "बिजली गिर", "बादल फट", "हिमस्खलन",
    "বন্যা", "ভূমিধস", "ভূমিকম্প", "ঘূর্ণিঝড়", "বজ্রপাত", "வெள்ளம்", "நிலச்சரிவு",
    "నిలநடுக்கம்", "వరద", "కొండచరియ", "భూకంపం", "ಪ್ರವಾಹ", "ಭೂಕುಸಿತ", "ಭೂಕಂಪ",
    "വെള്ളപ്പൊക്കം", "ഉരുൾപൊട്ടൽ", "ഭൂകമ്പം", "પૂર", "ભૂસ્ખલન", "ધરતીકંપ", "ਹੜ੍ਹ", "ਭੂਚਾਲ"]


def _has(text, words):
    return any(w in text for w in words)


def accident_verdict(text):
    if not text:
        return "unclear"
    if NOT_ACCIDENT.search(text) or _has(text, NOT_ACCIDENT_NATIVE):
        return "not_accident"
    if NATURAL_HAZARD.search(text) or _has(text, NATURAL_NATIVE):
        return "natural"
    if ACCIDENT_EVENT.search(text) or _has(text, ACCIDENT_NATIVE):
        return "accident"
    return "unclear"


# ===========================================================================
# GATE 4 - CURRENT EVENT REPORT?
# ===========================================================================
OLD_EVENT = re.compile(
    r"\b(?:19\d{2}|200\d|201\d|202[0-5])\b|"
    r"\b\d{1,3}\s*(?:years?|yrs?|decades?)\s+(?:ago|after|since|of|on)\b|"
    r"\b(?:anniversary|remembering|looking back|flashback|history of|"
    r"back in (?:19|20)\d{2}|that fateful|even after)\b", re.I)

NOT_EVENT_REPORT = re.compile(
    r"\b(?:investigation|investigating|probe|inquiry|enquiry|hearing|report (?:says|reveals)|"
    r"editorial|opinion|analysis|explainer|spotlight|questions? (?:on|raised)|why (?:does|did)|"
    r"demands?|urges|appeals|assures|announces|announced|launch(?:es|ed)|inaugurat\w*|"
    r"scheme|policy|guideline|bill |budget|tender|audit|mock drill|awareness|campaign|"
    r"safety week|training|workshop|seminar|conference|summit|meeting|"
    r"statistics|data shows|figures show|per day|per year|every hour|on average|"
    r"in (?:one|a|the last|the past|first)\s*\d{0,3}\s*(?:month|months|year|years|day|days)|"
    r"across the (?:country|state)|govt informs|assembly told|"
    r"drug test|dope test|breathalyser|licence suspended|grounded|"
    r"insurance|claim settled|acquitted|convicted|sentenced|"
    r"tells? parliament|told (?:in )?parliament|government (?:says|reveals|told)|"
    r"black box|aaib|dgca (?:said|report)|final payout|compensation|"
    r"revelation|reveals|big information|what was the reason|when will the truth|"
    r"survivor|survived|families? (?:of|grapple|asked|fears)|relatives of|"
    r"martyred|funeral|last rites|panchatatva|tricolor|sacrificed (?:his|her) life|"
    r"changed (?:his|her|their) (?:life|fate)|still has not forgotten|"
    r"sets model|teamwork|controversy over|questions? raised|"
    r"victim(?:'s)? (?:family|fate|story)|changed (?:his|her|their) family|"
    r"life of|don't have the courage|do not have the courage|"
    r"how .{0,30}(?:changed|coped|survived)|the death of|way of the death|"
    r"perfect wedding|hours after saying|my son was|newlywed|"
    r"tribute|remembers|recalls|looks back|has (?:not|never) forgot\w*|"
    r"stirred by|claims of|hidden in the .{0,20}report|"
    r"asked for|will not be made public|not caused by|did not happen due to)\b", re.I)


def currency_verdict(text, published_date):
    if not text:
        return "not_event"
    if NOT_EVENT_REPORT.search(text):
        return "not_event"
    if OLD_EVENT.search(text):
        return "old"
    if MIN_DATE and published_date and published_date < MIN_DATE:
        return "old"
    return "current"


# ===========================================================================
# THE GATE CHAIN
# ===========================================================================
def screen(title, snippet, source, url, published_date):
    """(True, '') to keep; (False, reason) to drop. Silence is rejection."""
    text = ((title or "") + " " + (snippet or "")).strip()
    if not text:
        return False, "empty"
    sv = source_verdict(source, url)
    if sv == "foreign":
        return False, "foreign_source"
    iv = india_verdict(text)
    if iv == "foreign":
        return False, "foreign_place"
    if iv != "india" and sv != "indian":
        return False, "india_unproven"
    av = accident_verdict(text)
    if av == "not_accident":
        return False, "not_an_accident"
    if av == "natural":
        return False, "natural_hazard"
    if av != "accident":
        return False, "no_accident_evidence"
    cv = currency_verdict(text, published_date)
    if cv == "old":
        return False, "old_event"
    if cv == "not_event":
        return False, "not_event_report"
    return True, ""


# ===========================================================================
# CLASSIFICATION
# ===========================================================================
CATEGORY_RULES = OrderedDict([
    # ORDER MATTERS AND IS DELIBERATE.
    # Construction is tested FIRST: a launching girder that falls onto a road
    # during metro work is a construction accident, not a road accident, and a
    # worker killed at a bridge site is construction even though 'bridge' would
    # otherwise read as a structure. Existing-structure failure is tested next
    # so that a road caving in is a structure failure, not a traffic accident.
    # Only then do the transport modes apply.
    ("construction_ongoing", re.compile(
        # --- project / site context ---------------------------------------
        r"\b(?:under[- ]construction|construction site|construction work|construction activity|"
        r"being (?:built|constructed|erected|laid|dug|widened)|under (?:repair|renovation|"
        r"widening|expansion|erection|execution)|newly (?:built|constructed)|ongoing (?:work|"
        r"project|construction)|work (?:site|in progress|zone)|project site|worksite|job site|"
        r"greenfield|brownfield|site office|labour camp|"
        # --- plant, equipment, temporary works -----------------------------
        r"crane|cranes|crawler crane|tower crane|mobile crane|launching girder|launcher|girder|"
        r"gantry|straddle carrier|scaffold\w*|staging|shuttering|deshuttering|formwork|"
        r"falsework|centering|props|jack ?post|cuplock|hoist|man ?hoist|winch|derrick|"
        r"boom lift|scissor lift|man ?lift|cradle|gondola|jhula|bosun chair|"
        r"batching plant|transit mixer|concrete pump|boom placer|vibrator|"
        r"piling|pile driver|bore pile|rig|excavator|jcb|backhoe|bulldozer|dozer|"
        r"road roller|paver|grader|tipper at site|dumper at site|"
        # --- earthworks -----------------------------------------------------
        r"excavat\w*|trench|trenching|pit collaps\w*|soil collaps\w*|earth caved|shoring|"
        r"benching|sloping|dewatering|borewell drilling|tunnel(?:ling|boring)|tbm\b|"
        r"blasting at site|rock cutting|embankment work|cutting slope|"
        # --- reinforcement and concrete ------------------------------------
        r"rebar|re-?bar|reinforcement|binding wire|steel fixing|bar bending|cutting bar|"
        r"tmt bar|stirrup|concreting|concrete pour|slab casting|casting yard|"
        r"segment (?:erection|casting)|precast|post-?tensioning|pre-?stress\w*|grouting|"
        r"curing|column casting|footing|raft|pile cap|"
        # --- finishing and other trades ------------------------------------
        r"chipping|plaster\w*|painting work|whitewash\w*|putty work|tiling|flooring work|"
        r"welding|gas cutting|grinding|cutting wheel|drilling work|carpentry|"
        r"masonry|brickwork|glazing|facade work|cladding|waterproofing|"
        r"electrical work|wiring work|conduit|ducting|plumbing work|"
        r"lift installation|erection work|dismantl\w*|demolition|deconstruction|"
        # --- workers and roles ---------------------------------------------
        r"construction (?:worker|labour|labor|labourer|laborer)|site (?:worker|engineer|"
        r"supervisor|in-?charge|manager)|mason|mistri|beldar|helper at site|"
        r"contractor|sub-?contractor|petty contractor|migrant labour\w*|"
        r"labourers? (?:at|working|engaged|died|killed)|workers? (?:at the )?site|"
        r"safety (?:harness|belt|net|helmet)|ppe\b|fall protection|"
        # --- named project types -------------------------------------------
        r"metro (?:work|project|construction|site|corridor|viaduct)|"
        r"flyover (?:work|construction|project)|bridge (?:work|construction|project)|"
        r"road (?:work|construction|widening|project)|highway (?:work|construction|project)|"
        r"station (?:work|construction)|building (?:work|construction)|"
        r"dam (?:work|construction)|canal (?:work|lining)|pipeline (?:work|laying)|"
        r"sewer(?:age)? (?:work|line laying)|water line laying|cable laying|"
        r"power (?:plant|project) (?:work|construction)|refinery (?:work|construction)|"
        r"expressway (?:work|construction|project)|smart city (?:work|project))\b"
        # --- native scripts -------------------------------------------------
        r"|निर्माणाधीन|निर्माण कार्य|निर्माण स्थल|निर्माण साइट|निर्माण मजदूर|क्रेन|मचान|खुदाई|"
        r"गड्ढा खोद|सरिया|शटरिंग|ढलाई|प्लास्टर|वेल्डिंग|ठेकेदार|मजदूर काम|मेट्रो निर्माण|"
        r"पुल निर्माण|सड़क निर्माण|गर्डर|"
        r"নির্মীয়মাণ|নির্মাণ কাজ|নির্মাণস্থল|ক্রেন|ভারা|খননের|শ্রমিক কাজ|ঠিকাদার|ঢালাই|"
        r"बांधकाम|क्रेन|मजूर|कंत्राटदार|खोदकाम|"
        r"கட்டுமான|கிரேன்|சாரம்|தொழிலாளர் பணி|ஒப்பந்ததாரர்|தோண்ட|"
        r"నిర్మాణంలో|నిర్మాణ పనులు|క్రేన్|కూలీలు పని|కాంట్రాక్టర్|తవ్వక|"
        r"ನಿರ್ಮಾಣ|ಕ್ರೇನ್|ಕಾರ್ಮಿಕರು|ಗುತ್ತಿಗೆದಾರ|ಅಗೆತ|"
        r"നിർമാണ|ക്രെയിൻ|തൊഴിലാളി|കരാറുകാരൻ|കുഴി|"
        r"બાંધકામ|ક્રેન|મજૂર|કોન્ટ્રાક્ટર|ખોદકામ|"
        r"ਉਸਾਰੀ|ਕਰੇਨ|ਮਜ਼ਦੂਰ|ਠੇਕੇਦਾਰ|ਪੁਟਾਈ", re.I)),
    ("old_structure_collapse", re.compile(
        r"\b(?:building|house|hut|wall|boundary wall|roof|slab|ceiling|balcony|staircase|"
        r"stairs|parapet|pillar|column|beam|lintel|chimney|tower|mast|hoarding|billboard|"
        r"bridge|culvert|overbridge|foot ?over ?bridge|flyover|underpass|subway|"
        r"structure|dilapidated|old building|godown|warehouse|shed|silo|tank|"
        r"road (?:cave[sd]?|caving|cave-?in|collaps\w*|sank|sunk|subsid\w*|settl\w*|sinkhole)|"
        r"sinkhole|cave-?in|land subsidence|retaining wall|embankment|"
        r"canal breach|dam breach|reservoir wall)\b"
        r"|इमारत|मकान|दीवार|छत|पुल|भवन|होर्डिंग|सड़क धंस|धंसी|"
        r"ভবন|বাড়ি|দেয়াল|ছাদ|সেতু|রাস্তা ধস|"
        r"भिंत|इमारत|पूल|रस्ता खचला|"
        r"கட்டிடம்|சுவர்|பாலம்|சாலை சரிவு|"
        r"భవనం|గోడ|వంతెన|రోడ్డు కుంగ|"
        r"ಕಟ್ಟಡ|ಗೋಡೆ|ಸೇತುವೆ|ರಸ್ತೆ ಕುಸಿ|"
        r"കെട്ടിടം|ഭിത്തി|പാലം|റോഡ് ഇടിഞ്ഞ|"
        r"ઇમારત|દીવાલ|પુલ|રસ્તો ધસી|"
        r"ਇਮਾਰਤ|ਕੰਧ|ਪੁਲ|ਸੜਕ ਧਸ", re.I)),
    ("aviation", re.compile(
        r"\b(?:aircraft|aeroplane|airplane|plane|helicopter|chopper|microlight|glider|"
        r"air ?crash|crash landing|emergency landing|runway excursion)\b"
        r"|विमान|हेलिकॉप्टर|বিমান|হেলিকপ্টার|விமான|విమానం|ವಿಮಾನ|വിമാനം|વિમાન|ਜਹਾਜ਼", re.I)),
    ("port_maritime", re.compile(
        r"\b(?:boat|boats|ferry|ferries|ship|ships|vessel|trawler|barge|steamer|"
        r"dredger|tugboat|harbour|harbor|jetty|dockyard|shipyard|seaport)\b"
        r"|नाव|नौका|जहाज|बंदरगाह|নৌকা|জাহাজ|লঞ্চ|বন্দর|படகு|கப்பல்|పడవ|నౌక|ದೋಣಿ|ಹಡಗು|ബോട്ട്|હોડી|ਕਿਸ਼ਤੀ", re.I)),
    ("train", re.compile(
        r"\b(?:train|trains|railway|railways|rail|locomotive|derail\w*|level crossing|"
        r"railway crossing|goods train|express train|metro rail|bogie|vande bharat|rajdhani|shatabdi|duronto|garib rath|emu|memu|local train|passenger train|mail express|superfast)\b"
        r"|ट्रेन|रेल|রেল|ট্রেন|ரயில்|రైలు|ರೈಲು|ട്രെയിൻ|ટ્રેન|ਰੇਲ", re.I)),
    ("roadway", re.compile(
        r"\b(?:road|roads|highway|expressway|street|bus|buses|truck|trucks|lorry|lorries|"
        r"tanker|trailer|car|cars|jeep|suv|van|tempo|auto|autorickshaw|auto-rickshaw|"
        r"rickshaw|bike|bikes|motorcycle|motorbike|scooter|scooty|two-wheeler|cyclist|"
        r"pedestrian|dumper|container|traffic|divider|vehicle|vehicles|airport road|hit from behind|hit-and-run)\b"
        r"|सड़क|हाईवे|बस|ट्रक|कार|बाइक|स्कूटर|রাস্তা|সড়ক|বাস|ট্রাক|গাড়ি|रस्ता|महामार्ग|"
        r"சாலை|பேருந்து|லாரி|கார்|రోడ్డు|బస్సు|ట్రక్|కారు|ರಸ್ತೆ|ಬಸ್|ಕಾರು|റോഡ്|ബസ്|കാർ|"
        r"માર્ગ|બસ|ટ્રક|કાર|ਸੜਕ|ਬੱਸ|ਟਰੱਕ|ਕਾਰ", re.I)),
    # ONGOING CONSTRUCTION - scoped as a safety programme would scope it:
    # ANY incident arising from construction activity, on ANY project (building,
    # road, bridge, metro, station, tunnel, dam, pipeline, plant), affecting
    # workers OR the public. Includes falls, struck-by, caught-between, crane and
    # girder failures, excavation and trench collapse, scaffold failure, formwork,
    # chipping, painting, welding, electrocution and site fires. A launching
    # girder that falls during metro work belongs here, not under "roadway".,
])



# The verb forms matter: "caves in", "gives way" and "falls" are as common in
# headlines as the past tense, and were being missed.
FAILURE_WORDS = re.compile(
    r"\b(?:collaps\w*|cave[sd]? in|caving in|cave-?in|give[sn]? way|gave way|"
    r"fall[s]?|fell|fallen|falling|sank|sunk|subsid\w*|settl(?:es|ed|ement)|"
    r"sinkhole|razed|crumbl\w*|gave in|buckl\w*|snapped|toppl\w*|"
    r"came (?:down|crashing)|broke (?:off|away))\b"
    r"|ढह|गिर|धंस|ধস|कोसळ|खचल|இடிந்து|சரிவு|కూలి|కుంగ|ಕುಸಿ|തകർ|ഇടിഞ്ഞ|ધરાશાયી|ધસી|ਢਹਿ|ਧਸ", re.I)

OTHER_SECTORS = OrderedDict([
    ("factory_manufacturing", re.compile(r"\b(?:factory|plant|mill|workshop|boiler|furnace|foundry|manufactur\w*)\b|फैक्ट्री|कारखाना|কারখানা|தொழிற்சாலை|ఫ్యాక్టరీ|ಕಾರ್ಖಾನೆ|ഫാക്ടറി|ફેક્ટરી|ਫੈਕਟਰੀ", re.I)),
    ("mining_quarry", re.compile(r"\b(?:mine|mines|mining|colliery|quarry|stone crusher)\b|खदान|खनन|খনি|சுரங்க|గని|ಗಣಿ|ഖനി|ખાણ", re.I)),
    ("chemical_refinery", re.compile(r"\b(?:chemical|refinery|petrochemical|acid|ammonia|chlorine)\b|रासायनिक|রাসায়নিক|ரசாயன|రసాయన", re.I)),
    ("fireworks_explosives", re.compile(r"\b(?:firecracker|cracker unit|fireworks|explosive)\b|पटाखा|আতশবাজি|পটকা|பட்டாசு|బాణాసంచా", re.I)),
    ("gas_cylinder", re.compile(r"\b(?:gas leak|cylinder|lpg|gas pipeline)\b|गैस|গ্যাস|எரிவாயு|గ్యాస్", re.I)),
    ("electrical", re.compile(r"\b(?:electrocut\w*|live wire|transformer|short circuit|high tension)\b|करंट|बिजली|বিদ্যুৎ|மின்சார|విద్యుత్", re.I)),
    ("fire", re.compile(r"\b(?:fire|blaze|gutted)\b|आग|আগুন|தீ|మంటలు|ಬೆಂಕಿ|തീ", re.I)),
    ("sewer_sanitation", re.compile(r"\b(?:septic tank|sewer|manhole|drain)\b|सेप्टिक|सीवर|নর্দমা", re.I)),
    ("borewell_well", re.compile(r"\b(?:borewell|bore well|open well)\b|बोरवेल|কূপ", re.I)),
    ("lift_elevator", re.compile(r"\b(?:lift|elevator|escalator)\b|लिफ्ट|লিফট", re.I)),
    ("agriculture", re.compile(r"\b(?:tractor|harvester|thresher)\b|ट्रैक्टर|ট্রাক্টর|டிராக்டர்", re.I)),
    ("amusement_ride", re.compile(r"\b(?:ferris wheel|giant wheel|joy ?ride|amusement|fair ride|"
                                  r"roller coaster|merry-go-round|swing ride)\b|झूला|নাগরদোলা", re.I)),
])


ROAD_EVENT = re.compile(
    r"\b(?:road accident|road mishap|road crash|hit by a (?:car|bus|truck|bike|vehicle)|"
    r"run over|knocked down)\b|सड़क हादसा|सड़क दुर्घटना|সড়ক দুর্ঘটনা|रस्ता अपघात|"
    r"சாலை விபத்து|రోడ్డు ప్రమాదం|ರಸ್ತೆ ಅಪಘಾತ|റോഡ് അപകടം|માર્ગ અકસ્માત|ਸੜਕ ਹਾਦਸਾ", re.I)
AIRCRAFT_EVENT = re.compile(
    r"\b(?:plane|aircraft|aeroplane|airplane|helicopter|chopper|microlight|glider)\b"
    r".{0,60}?\b(?:crash\w*|collid\w*|collision|land\w*|overshot|skidd\w*|caught fire|"
    r"engine|malfunction\w*|averted)\b"
    r"|\b(?:crash|collision|collid\w*|averted)\b.{0,60}?"
    r"\b(?:plane|aircraft|aeroplane|helicopter|chopper|microlight)\b", re.I)


def classify(text):
    for cat, pat in CATEGORY_RULES.items():
        if pat.search(text):
            if cat == "old_structure_collapse" and not FAILURE_WORDS.search(text):
                continue          # a structure word alone is not a collapse
            if cat == "aviation":
                # The Tamil/Telugu words for "airport" contain the word for
                # "aircraft", so a road accident involving an airport worker was
                # being filed as aviation. Require a genuine aircraft event, and
                # never override an explicit road accident.
                if ROAD_EVENT.search(text) and not AIRCRAFT_EVENT.search(text):
                    continue
                if not AIRCRAFT_EVENT.search(text):
                    continue
            return cat, ""
    for sector, pat in OTHER_SECTORS.items():
        if pat.search(text):
            return "others", sector
    return "others", "unspecified"


# ===========================================================================
# FACT EXTRACTION
# ===========================================================================
def _digit_map():
    m = {}
    for s in [0x0966, 0x09E6, 0x0A66, 0x0AE6, 0x0B66, 0x0BE6, 0x0C66, 0x0CE6, 0x0D66]:
        for d in range(10):
            m[chr(s + d)] = str(d)
    return str.maketrans(m)

DIGITS = _digit_map()

WORD_NUM = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6, "seven": 7,
            "eight": 8, "nine": 9, "ten": 10, "eleven": 11, "twelve": 12,
            "एक": 1, "दो": 2, "तीन": 3, "चार": 4, "पांच": 5, "पाँच": 5, "छह": 6, "सात": 7,
            "এক": 1, "দুই": 2, "তিন": 3, "চার": 4, "পাঁচ": 5,
            "இரண்டு": 2, "மூன்று": 3, "நான்கு": 4, "ஐந்து": 5,
            "ఇద్దరు": 2, "ముగ్గురు": 3, "నలుగురు": 4, "ఐదుగురు": 5, "ఏడుగురు": 7,
            "ఐదుగురికి": 5, "ఏడుగురికి": 7, "ಇಬ್ಬರು": 2, "ಮೂವರು": 3, "બે": 2, "ਦੋ": 2}

DEATH_CUES = ["killed", "kills", "dead", "death", "deaths", "died", "dies", "deceased",
              "lost life", "lives lost", "मौत", "मृत", "मरे", "मृत्यु", "ठार",
              "নিহত", "মৃত", "মৃত্যু", "இறந்த", "உயிரிழ", "பலி", "మృతి", "మరణ", "చనిపో",
              "ಸಾವು", "ಮೃತ", "ಬಲಿ", "മരണം", "മരിച്ച", "મોત", "મૃત્યુ", "ਮੌਤ", "ਮਰੇ"]
INJURY_CUES = ["injured", "hurt", "wounded", "injuries", "घायल", "जख्मी", "আহত", "জখম",
               "जखमी", "காயம்", "படுகாயம்", "గాయ", "ಗಾಯ", "പരിക്ക", "ઘાયલ", "ਜ਼ਖ਼ਮੀ"]

ANIMALS = re.compile(r"\b(?:sheep|goats?|cattle|cows?|buffalo\w*|bulls?|dogs?|cats?|"
                     r"elephants?|monkeys?|birds?|hens?|pigs?|horses?|camels?|livestock|animals?)\b", re.I)
HUMANS = re.compile(r"\b(?:people|persons?|passengers?|men|man|women|woman|children|child|"
                    r"boys?|girls?|workers?|labourers?|students?|drivers?|pedestrians?|"
                    r"villagers?|farmers?|devotees?|pilgrims?|jawans?|police\w*|tourists?|"
                    r"youths?|family|victims?|nationals?)\b", re.I)


def _clean_numbers(text):
    t = text.translate(DIGITS)
    t = re.sub(r"\|\s*\d+\s*$", " ", t)
    t = re.sub(r"\b(?:nh|sh|mdr|national highway|state highway|route)\s*[-\u2013]?\s*\d+[a-z]?\b", " ", t, flags=re.I)
    t = re.sub(r"\b\d{1,3}\s*[-\u2013]?\s*(?:year|yr|yrs|years)\s*[-\u2013]?\s*old\b", " ", t, flags=re.I)
    t = re.sub(r"\b(?:aged|age)\s*\d{1,3}\b", " ", t, flags=re.I)
    t = re.sub(r"\b([A-Za-z]+)\s*,\s*\d{1,3}\s*,", r" \1 ", t)
    t = re.sub(r"\b\d+(?:\.\d+)?\s*(?:%|per\s*cent|percent)", " ", t, flags=re.I)
    t = re.sub(r"\b\d+\s*(?:km|kms|metre|meter|feet|ft|storey|storeys|floor|floors|"
               r"minute|minutes|hour|hours|day|days|week|weeks|month|months|year|years|"
               r"am|pm|lakh|crore)\b", " ", t, flags=re.I)
    t = re.sub(r"\b\d{1,3}\s*[x\u00d7]\s*\d{1,2}\b", " ", t)
    t = re.sub(r"(?<=\d)[,.](?=\d{3}\b)", "", t)
    low = t.lower()
    for w, v in sorted(WORD_NUM.items(), key=lambda kv: -len(kv[0])):
        if w in low:
            low = (re.sub(r"\b" + re.escape(w) + r"\b(?![-\w])", f" {v} ", low)
                   if w.isascii() else low.replace(w, f" {v} "))
    return low


def extract_counts(text):
    t = _clean_numbers(text)

    def near(cues, window=34):
        best = None
        for cue in cues:
            start = 0
            while True:
                i = t.find(cue.lower(), start)
                if i == -1:
                    break
                lo, hi = max(0, i - window), min(len(t), i + len(cue) + window)
                while lo > 0 and t[lo - 1].isdigit():
                    lo -= 1
                while hi < len(t) and t[hi].isdigit():
                    hi += 1
                seg = t[lo:hi]
                for mm in re.finditer(r"\d+", seg):
                    val = int(mm.group())
                    if val <= 0 or val > 500 or 1900 <= val <= 2100:
                        continue
                    after = seg[mm.end(): mm.end() + 26]
                    am, hm = ANIMALS.search(after), HUMANS.search(after)
                    if am and (not hm or am.start() < hm.start()):
                        continue
                    pos = mm.start() + lo
                    dist = abs(pos - i) * (2.0 if pos > i else 1.0)
                    if best is None or dist < best[0]:
                        best = (dist, val, pos)
                start = i + len(cue)
        return best

    d, i = near(DEATH_CUES), near(INJURY_CUES)
    if d and i and d[2] == i[2]:
        if d[0] <= i[0]:
            i = None
        else:
            d = None
    return (d[1] if d else None), (i[1] if i else None)


HIGHWAY_RE = [re.compile(r"\bNH[-\s]?\d{1,3}[A-Z]?\b", re.I),
              re.compile(r"\bSH[-\s]?\d{1,3}[A-Z]?\b", re.I),
              re.compile(r"\b[A-Z][a-z]+(?:[-\s][A-Z][a-z]+)?\s+Expressway\b")]

JUNK_PLACES = {"google", "news", "india", "indian", "bharat", "video", "watch", "live",
               "update", "breaking", "exclusive", "hindi", "bengali", "marathi", "tamil",
               "telugu", "kannada", "malayalam", "gujarati", "punjabi", "maratha"}


def extract_places(text):
    if not text:
        return "", ""
    found, seen = [], set()
    for name, pat in _PLACE_PATTERNS:
        if name.lower() in JUNK_PLACES or name.lower() in seen:
            continue
        if pat.search(text):
            found.append(name)
            seen.add(name.lower())
            if len(found) >= 3:
                break
    hw, hs = [], set()
    for pat in HIGHWAY_RE:
        for m in pat.findall(text):
            k = re.sub(r"[-\s]+", "-", m.strip())
            if k.lower() not in hs:
                hw.append(k)
                hs.add(k.lower())
    return "; ".join(found), "; ".join(hw)


CAUSE_TRIGGER = re.compile(
    r"\b(?:after|when|while|due to|because of|owing to|caused by|as a result of|"
    r"following|reportedly|allegedly|suspected|police said|prima facie|lost control|"
    r"brake failure|tyre burst|overspeed\w*|drunk|asleep|fog|slipp\w*|overload\w*|negligen\w*)\b", re.I)
SENT_SPLIT = re.compile(r"(?<=[.!?])\s+|\u0964")


def extract_cause(body, headline):
    """Explanation taken from the article body, with sentences that merely
    restate the headline removed. Blank when the report does not explain."""
    if not body:
        return ""
    text = re.sub(r"\s+", " ", body).strip()
    sents = [s.strip() for s in SENT_SPLIT.split(text) if len(s.strip()) > 25]
    hw = set(re.findall(r"[a-z]{4,}", (headline or "").lower()))
    keep = []
    for s in sents[:10]:
        sw = set(re.findall(r"[a-z]{4,}", s.lower()))
        if hw and sw and len(hw & sw) / max(1, min(len(hw), len(sw))) >= 0.6:
            continue
        if CAUSE_TRIGGER.search(s):
            keep.append(s)
        if sum(len(k.split()) for k in keep) > 55:
            break
    return " ".join(keep).strip()[:400]


TIME_AMPM = re.compile(r"\b(\d{1,2})(?::(\d{2}))?\s*(am|pm|a\.m\.|p\.m\.)\b", re.I)
TIME_24 = re.compile(r"\b([01]?\d|2[0-3]):([0-5]\d)\s*(?:hrs|hours)?\b")
NIGHT_WORDS = ["night", "midnight", "wee hours", "early hours", "overnight", "evening",
               "रात", "शाम", "রাত", "সন্ধ্যা", "இரவு", "மாலை", "రాత్రి", "సాయంత్రం",
               "ರಾತ್ರಿ", "ಸಂಜೆ", "രാത്രി", "વૈകുന്നേരം", "રાત", "સાંજ", "ਰਾਤ", "ਸ਼ਾਮ"]
DAY_WORDS = ["morning", "afternoon", "noon", "midday", "daytime", "सुबह", "दोपहर", "सकाळ",
             "সকাল", "দুপুর", "காலை", "மதியம்", "ఉదయం", "మధ్యాహ్నం", "ಬೆಳಿಗ್ಗೆ", "ಮಧ್ಯಾಹ್ನ",
             "രാവിലെ", "ઉച്ച", "સવાર", "બપોર", "ਸਵੇਰ", "ਦੁਪਹਿਰ"]


def extract_time_of_day(text):
    if not text:
        return ""
    m = TIME_AMPM.search(text)
    if m:
        h = int(m.group(1)) % 12
        if m.group(3).lower().startswith("p"):
            h += 12
        return "Night" if (h >= 18 or h < 6) else "Day"
    m = TIME_24.search(text)
    if m:
        h = int(m.group(1))
        return "Night" if (h >= 18 or h < 6) else "Day"
    low = text.lower()
    if any(w in low for w in NIGHT_WORDS):
        return "Night"
    if any(w in low for w in DAY_WORDS):
        return "Day"
    return ""


MALE_RE = re.compile(r"\b(?:man|men|male|boy|boys|father|husband|son|brother|youth|jawan)\b", re.I)
FEMALE_RE = re.compile(r"\b(?:woman|women|female|girl|girls|mother|wife|daughter|sister|lady)\b", re.I)
AGE_RE = [re.compile(r"\b(\d{1,3})\s*[-\u2013]?\s*(?:year|yr|yrs|years)\s*[-\u2013]?\s*old\b", re.I),
          re.compile(r"\b(?:aged|age)\s*(\d{1,3})\b", re.I)]


def extract_gender(text):
    if not text:
        return ""
    m, f = bool(MALE_RE.search(text)), bool(FEMALE_RE.search(text))
    return "Both" if m and f else ("Male" if m else ("Female" if f else ""))


def extract_ages(text):
    out = []
    for pat in AGE_RE:
        for v in pat.findall(text or ""):
            n = int(v)
            if 0 < n <= 110 and n not in out:
                out.append(n)
    return "; ".join(str(x) for x in sorted(out)[:4])


NEAR_MISS = re.compile(
    r"\b(?:no casualt\w*|no one (?:was )?(?:hurt|injured)|nobody injured|no injuries|"
    r"escaped unhurt|escaped unharmed|narrow escape|narrowly escaped|averted|all safe|"
    r"rescued safely|no loss of life)\b|बाल-बाल बच|हादसा टला", re.I)


def severity(text, deaths, injured):
    if deaths:
        return "Fatal"
    if injured:
        return "Injury only"
    if text and NEAR_MISS.search(text):
        return "Near miss"
    return "Not stated"


# ===========================================================================
# TRANSLATION
# ===========================================================================
_MOCK_TRANSLATE = None


def translate_to_en(text):
    if not text or not text.strip():
        return ""
    if _MOCK_TRANSLATE is not None:
        return _MOCK_TRANSLATE(text)
    if TRANSLATE_BACKEND != "builtin":
        return ""
    try:
        url = ("https://translate.googleapis.com/translate_a/single"
               "?client=gtx&sl=auto&tl=en&dt=t&q=" + urllib.parse.quote(text[:1800]))
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=15) as r:
            data = json.loads(r.read().decode("utf-8", "ignore"))
        return "".join(seg[0] for seg in data[0] if seg and seg[0])
    except Exception:                                              # noqa: BLE001
        return ""


# ===========================================================================
# HTTP / FEEDS
# ===========================================================================
def http_get(url, timeout=30, retries=2):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    for a in range(retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read(), r.geturl()
        except Exception:                                          # noqa: BLE001
            if a == retries - 1:
                return None, None
            time.sleep(2)
    return None, None


GOOGLE_BOILERPLATE = ["comprehensive up-to-date news coverage",
                      "aggregated from sources all over the world",
                      "read full articles, watch videos"]


def is_boilerplate(text):
    if not text or len(text) < 40:
        return True
    low = text.lower()
    return any(b in low for b in GOOGLE_BOILERPLATE)


def resolve_url(url):
    if "news.google.com" not in url:
        return url
    m = re.search(r"/articles/([A-Za-z0-9_\-]+)", url)
    if not m:
        return ""
    try:
        tok = m.group(1)
        raw = base64.urlsafe_b64decode((tok + "=" * (-len(tok) % 4)).encode("ascii"))
        f = re.search(rb"https?://[^\x00-\x20\"'<>]{10,}", raw)
        if f:
            cand = f.group(0).decode("utf-8", "ignore")
            if "google.com" not in cand:
                return cand
    except Exception:                                              # noqa: BLE001
        pass
    return ""


PARA_RE = re.compile(r"<p[^>]*>(.*?)</p>", re.I | re.S)
TAG_RE = re.compile(r"<[^>]+>")
OG_IMG = re.compile(r'<meta[^>]+og:image["\'][^>]+content=["\']([^"\']+)["\']', re.I)


def fetch_article(url, max_chars=1400):
    real = resolve_url(url)
    if not real:
        return "", "", ""
    data, final = http_get(real, timeout=FETCH_TIMEOUT, retries=1)
    if not data or "news.google.com" in (final or ""):
        return "", "", ""
    page = data.decode("utf-8", "ignore")
    img = OG_IMG.search(page)
    parts = []
    for p in PARA_RE.findall(page)[:14]:
        t = re.sub(r"\s+", " ", html.unescape(TAG_RE.sub(" ", p))).strip()
        if len(t) > 60 and not t.lower().startswith(("subscribe", "follow us", "also read",
                                                     "read more", "advertisement", "copyright")):
            parts.append(t)
        if sum(len(x) for x in parts) > max_chars:
            break
    body = " ".join(parts)[:max_chars]
    if is_boilerplate(body):
        return final or "", "", ""
    return (final or ""), (html.unescape(img.group(1)) if img else ""), body


def dedupe_title(t):
    if not t:
        return ""
    t = re.sub(r"\s+", " ", t.replace("\n", " ")).strip()
    half = len(t) // 2
    lo, hi = max(20, half - 30), min(max(21, len(t) - 15), half + 30)
    for cut in range(lo, hi):
        a, b = t[:cut].strip(), t[cut:].strip()
        if len(b) > 12 and (a.lower().startswith(b.lower()[:18]) or b.lower().startswith(a.lower()[:18])):
            return a
    return t


def norm_title(t):
    t = (t or "").lower()
    t = re.sub(r"\s+-\s+[^-]+$", "", t)
    t = re.sub(r"[^\w\u0900-\u0d7f ]", " ", t, flags=re.UNICODE)
    return re.sub(r"\s+", " ", t).strip()


def parse_date(raw):
    if raw:
        try:
            dt = parsedate_to_datetime(raw)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.timestamp(), dt.strftime("%Y-%m-%d")
        except (TypeError, ValueError):
            pass
    now = datetime.now(timezone.utc)
    return now.timestamp(), now.strftime("%Y-%m-%d")


def parse_feed(xml_bytes, language, query):
    out = []
    if not xml_bytes:
        return out
    try:
        root = ElementTree.fromstring(xml_bytes)
    except ElementTree.ParseError:
        return out
    for item in root.iter("item"):
        title = dedupe_title((item.findtext("title") or "").strip())
        if not title:
            continue
        desc = re.sub(r"<[^>]+>", " ", item.findtext("description") or "").strip()
        src_el = item.find("source")
        ts, iso = parse_date((item.findtext("pubDate") or "").strip())
        out.append({"title": title, "snippet": desc[:400],
                    "url": (item.findtext("link") or "").strip(),
                    "source": src_el.text.strip() if src_el is not None and src_el.text else "",
                    "language": language, "query": query,
                    "published": iso, "published_ts": ts})
    return out


# ===========================================================================
# DATABASE
# ===========================================================================
COLUMNS = OrderedDict([
    ("id", "TEXT PRIMARY KEY"), ("title", "TEXT"), ("title_en", "TEXT"), ("url", "TEXT"),
    ("source", "TEXT"), ("published", "TEXT"), ("published_ts", "REAL"),
    ("category", "TEXT"), ("sector", "TEXT"), ("language", "TEXT"), ("title_norm", "TEXT"),
    ("snippet", "TEXT"), ("article_text", "TEXT"), ("image_url", "TEXT"),
    ("cities", "TEXT"), ("highways", "TEXT"), ("deaths", "INTEGER"), ("injured", "INTEGER"),
    ("cause", "TEXT"), ("time_of_day", "TEXT"), ("victim_gender", "TEXT"), ("victim_age", "TEXT"),
    ("severity", "TEXT"), ("fetched_at", "TEXT"), ("is_duplicate", "INTEGER DEFAULT 0"),
    ("dup_group", "TEXT"), ("translated", "INTEGER DEFAULT 0"),
])


def init_db(conn):
    conn.execute(f"CREATE TABLE IF NOT EXISTS articles ({', '.join(f'{k} {v}' for k, v in COLUMNS.items())})")
    have = {r[1] for r in conn.execute("PRAGMA table_info(articles)")}
    for c, d in COLUMNS.items():
        if c not in have:
            conn.execute(f"ALTER TABLE articles ADD COLUMN {c} {d.replace(' PRIMARY KEY', '')}")
    conn.commit()


# ===========================================================================
# DEDUPLICATION
# ===========================================================================
STOPW = {"the", "and", "for", "with", "after", "near", "from", "were", "was", "has", "had",
         "accident", "accidents", "news", "video", "killed", "dead", "death", "died", "injured",
         "people", "person", "police", "said", "report", "update", "horrific", "terrible"}


def content_words(t):
    return {w for w in re.findall(r"[a-z]{4,}", (t or "").lower()) if w not in STOPW}


def similarity(a, b):
    parts, weights, strong = [], [], False
    ca = {x.strip().lower() for x in a["cities"].split(";") if x.strip()}
    cb = {x.strip().lower() for x in b["cities"].split(";") if x.strip()}
    ha = {x.strip().lower() for x in a["highways"].split(";") if x.strip()}
    hb = {x.strip().lower() for x in b["highways"].split(";") if x.strip()}
    loc = bool((ca and cb and ca & cb) or (ha and hb and ha & hb))
    wa, wb = a["words"], b["words"]
    ov = len(wa & wb) / max(1, min(len(wa), len(wb))) if wa and wb else 0.0

    da, db = a["deaths"], b["deaths"]
    if da is not None and db is not None:
        if da == db:
            parts.append(1.0); weights.append(0.40); strong = True
        elif abs(da - db) <= 1:
            parts.append(0.5); weights.append(0.40)
        elif loc and ov >= 0.40:
            parts.append(0.5); weights.append(0.15)
        else:
            parts.append(0.0); weights.append(0.40)
    if loc:
        parts.append(1.0); weights.append(0.30); strong = True
    elif (ca and cb) or (ha and hb):
        parts.append(0.0); weights.append(0.30)
    if ov >= 0.40:
        parts.append(ov); weights.append(0.35)
        if ov >= 0.50 and len(wa & wb) >= 3:
            strong = True
    r = SequenceMatcher(None, a["title_norm"], b["title_norm"]).ratio()
    parts.append(r); weights.append(0.25)
    if r >= TITLE_DUP_THRESHOLD:
        strong = True
    if not parts:
        return 0.0, False
    score = sum(p * w for p, w in zip(parts, weights)) / sum(weights)
    if loc and ov >= 0.50:
        score = max(score, 0.75)
        strong = True
    return score, strong


def rededupe(conn):
    conn.execute("UPDATE articles SET is_duplicate=0, dup_group=id")
    rows = conn.execute(
        """SELECT id,title_norm,cities,highways,deaths,injured,category,published_ts,title_en,title
           FROM articles ORDER BY published_ts ASC""").fetchall()
    seen, merged = [], 0
    for r in rows:
        a = {"id": r[0], "title_norm": r[1] or "", "cities": r[2] or "", "highways": r[3] or "",
             "deaths": r[4], "injured": r[5], "category": r[6], "published_ts": r[7] or 0,
             "words": content_words((r[8] or "") or (r[9] or "")), "dup_group": r[0]}
        best = None
        for b in seen:
            if b["category"] != a["category"]:
                continue
            if abs(b["published_ts"] - a["published_ts"]) > EVENT_DATE_WINDOW_DAYS * 86400:
                continue
            s, strong = similarity(a, b)
            if s >= EVENT_SIM_THRESHOLD and strong and (best is None or s > best[1]):
                best = (b["dup_group"], s)
        if best:
            conn.execute("UPDATE articles SET is_duplicate=1, dup_group=? WHERE id=?", (best[0], a["id"]))
            a["dup_group"] = best[0]
            merged += 1
        seen.append(a)
        if len(seen) > 3000:
            seen = seen[-3000:]
    conn.commit()
    print(f"[dedupe] {merged} duplicate reports merged")
    return merged


# ===========================================================================
# STORE
# ===========================================================================
def store(conn, items, stats, translate_budget=0):
    added = 0
    for it in items:
        keep, reason = screen(it["title"], it["snippet"], it["source"], it["url"], it["published"])
        if not keep:
            stats[reason] = stats.get(reason, 0) + 1
            continue

        title_en = ""
        if it["language"] != "English" and TRANSLATE_BACKEND != "none" and translate_budget > 0:
            title_en = translate_to_en(it["title"] + "\n" + it["snippet"])
            translate_budget -= 1
            if title_en:
                keep2, reason2 = screen(title_en, "", it["source"], it["url"], it["published"])
                if not keep2:
                    stats[reason2 + " (seen after translation)"] = \
                        stats.get(reason2 + " (seen after translation)", 0) + 1
                    continue

        full = it["title"] + " " + it["snippet"] + " " + title_en
        rid = hashlib.sha1(norm_title(it["title"]).encode("utf-8")).hexdigest()
        if conn.execute("SELECT 1 FROM articles WHERE id=?", (rid,)).fetchone():
            stats["already stored"] = stats.get("already stored", 0) + 1
            continue

        cat, sector = classify(full)
        deaths, injured = extract_counts(full)
        cities, highways = extract_places(title_en or full)
        conn.execute(
            """INSERT OR IGNORE INTO articles
               (id,title,title_en,url,source,published,published_ts,category,sector,language,
                title_norm,snippet,article_text,image_url,cities,highways,deaths,injured,cause,
                time_of_day,victim_gender,victim_age,severity,fetched_at,is_duplicate,dup_group,translated)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?,?)""",
            (rid, it["title"], title_en, it["url"], it["source"], it["published"],
             it["published_ts"], cat, sector, it["language"], norm_title(it["title"]),
             it["snippet"], "", "", cities, highways, deaths, injured, "",
             extract_time_of_day(full), extract_gender(title_en or full), extract_ages(full),
             severity(full, deaths, injured),
             datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), rid,
             1 if title_en else 0))
        added += 1
        stats["KEPT"] = stats.get("KEPT", 0) + 1
    conn.commit()
    return added, translate_budget


def backfill_articles(conn, budget):
    if budget <= 0:
        return 0
    rows = conn.execute(
        """SELECT id,url,title,title_en FROM articles
           WHERE (article_text IS NULL OR article_text='') AND url!=''
           ORDER BY published_ts DESC LIMIT ?""", (budget,)).fetchall()
    done = 0
    for rid, url, title, ten in rows:
        _, img, body = fetch_article(url)
        if not body:
            conn.execute("UPDATE articles SET article_text='-' WHERE id=?", (rid,))
            continue
        body_en = body
        if TRANSLATE_BACKEND != "none" and not body.isascii():
            body_en = translate_to_en(body[:1500]) or body
        keep, _ = screen((ten or title or "") + " " + body_en, "", "", url, None)
        if not keep:
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            continue
        full = (title or "") + " " + (ten or "") + " " + body + " " + body_en
        cities, highways = extract_places(body_en + " " + (ten or ""))
        deaths, injured = extract_counts(full)
        cat, sector = classify(full)          # the body often names the activity
        conn.execute(
            """UPDATE articles SET article_text=?, category=?, sector=?,
               image_url=CASE WHEN image_url='' THEN ? ELSE image_url END,
               cause=?, cities=CASE WHEN ?!='' THEN ? ELSE cities END,
               highways=CASE WHEN ?!='' THEN ? ELSE highways END,
               deaths=COALESCE(deaths,?), injured=COALESCE(injured,?),
               time_of_day=CASE WHEN time_of_day='' THEN ? ELSE time_of_day END,
               victim_gender=CASE WHEN victim_gender='' THEN ? ELSE victim_gender END,
               victim_age=CASE WHEN victim_age='' THEN ? ELSE victim_age END,
               severity=? WHERE id=?""",
            (body[:1400], cat, sector, img, extract_cause(body_en, ten or title),
             cities, cities, highways, highways, deaths, injured,
             extract_time_of_day(full), extract_gender(body_en), extract_ages(full),
             severity(full, deaths, injured), rid))
        done += 1
        time.sleep(0.25)
    conn.commit()
    if done:
        print(f"[articles] fetched and analysed {done}")
    return done


def rescreen_all(conn):
    """Apply the CURRENT gates to everything already stored, so a rule change
    cleans history instead of only affecting new items."""
    removed = 0
    for rid, title, ten, snip, body, src, url, pub in conn.execute(
            "SELECT id,title,title_en,snippet,article_text,source,url,published FROM articles").fetchall():
        clean = dedupe_title(title or "")
        text = " ".join(x for x in (clean, ten or "", snip or "",
                                    (body if body and body != "-" else "")) if x)
        keep, _ = screen(text, "", src or "", url or "", pub)
        if not keep:
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            removed += 1
            continue
        cat, sector = classify(text)
        cities, highways = extract_places((ten or "") + " " + text)
        conn.execute("""UPDATE articles SET title=?, title_norm=?, category=?, sector=?,
                        cities=?, highways=? WHERE id=?""",
                     (clean, norm_title(clean), cat, sector, cities, highways, rid))
    conn.commit()
    if removed:
        print(f"[rescreen] removed {removed} stored records that fail the current gates")
    return removed


# ===========================================================================
# EXPORTS
# ===========================================================================
def _w(path):
    return open(path, "w", newline="", encoding="utf-8-sig")


def export_accidents(conn, path="ACCIDENTS.csv"):
    """ONE ROW PER ACCIDENT. Duplicate reports are not in this file at all."""
    groups = {}
    for r in conn.execute(
            """SELECT dup_group,published,published_ts,category,sector,cities,highways,deaths,
                      injured,cause,time_of_day,victim_gender,victim_age,severity,source,
                      title,title_en,url,language
               FROM articles ORDER BY published_ts ASC"""):
        groups.setdefault(r[0], []).append(r)
    rows = []
    for members in groups.values():
        by_time = sorted(members, key=lambda x: x[2] or 0)
        first, last = by_time[0], by_time[-1]
        best = max(members, key=lambda r: (r[7] is not None) * 3 + (r[8] is not None) * 2
                   + bool(r[5]) * 2 + bool(r[9]) * 2 + (r[18] == "English"))
        deaths = next((x[7] for x in reversed(by_time) if x[7] is not None), None)
        injured = next((x[8] for x in reversed(by_time) if x[8] is not None), None)
        rows.append([
            first[1], last[1], (best[3] or "").replace("_", " "), (best[4] or "").replace("_", " "),
            best[5] or "", best[6] or "",
            deaths if deaths is not None else "", injured if injured is not None else "",
            best[13] or "", next((x[10] for x in members if x[10]), ""),
            next((x[11] for x in members if x[11]), ""), next((x[12] for x in members if x[12]), ""),
            next((x[9] for x in members if x[9]), ""), len(members),
            "; ".join(sorted({(x[14] or "").strip() for x in members if (x[14] or "").strip()})[:6]),
            best[15] or "", best[16] or "", best[17] or ""])
    rows.sort(key=lambda r: r[0], reverse=True)
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Date of Accident", "Last Reported", "Accident Type", "Sector (others only)",
                    "City / Place", "Highway", "Killed", "Injured", "Severity", "Time of Day",
                    "Victim Gender", "Victim Age(s)", "Reported Cause", "Times Reported",
                    "Reported By", "Headline", "Headline (English)", "Link"])
        w.writerows(rows)
    return len(rows)


def export_summary(conn, path, confirmed_only):
    agg = {}
    for cities, cat, sector, sev, d, i in conn.execute(
            """SELECT cities,category,sector,severity,deaths,injured
               FROM articles WHERE is_duplicate=0"""):
        places = [c.strip() for c in (cities or "").split(";") if c.strip()]
        place = places[0] if places else "Not identified"
        cat_l = (cat or "").replace("_", " ")
        sec_l = (sector or "").replace("_", " ")
        if confirmed_only:
            if not places or not cat_l:
                continue
            if cat == "others" and sec_l in ("", "unspecified"):
                continue
            if sev in ("", "Not stated", None):
                continue
        a = agg.setdefault((place, cat_l, sec_l),
                           {"n": 0, "near": 0, "fatal": 0, "inj": 0, "k": 0, "i": 0})
        a["n"] += 1
        a["near"] += sev == "Near miss"
        a["fatal"] += sev == "Fatal"
        a["inj"] += sev == "Injury only"
        a["k"] += d or 0
        a["i"] += i or 0
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["City", "Accident Type", "Sector (others only)", "Number of Accidents",
                    "Near Misses", "Fatal Accidents", "Injury-only Accidents",
                    "People Killed", "People Injured"])
        for (p, c, s), a in sorted(agg.items(), key=lambda kv: (-kv[1]["k"], -kv[1]["n"], kv[0][0])):
            w.writerow([p, c, s, a["n"], a["near"], a["fatal"], a["inj"], a["k"], a["i"]])
    return len(agg)


def export_monthly(conn, path="TREND_monthly.csv"):
    data, cats = {}, set()
    for mth, cat, n, k, i in conn.execute(
            """SELECT strftime('%Y-%m',published), category, COUNT(*),
                      COALESCE(SUM(deaths),0), COALESCE(SUM(injured),0)
               FROM articles WHERE is_duplicate=0 AND published!='' GROUP BY 1,2"""):
        data.setdefault(mth, {})[cat] = (n, k, i)
        cats.add(cat)
    cats = sorted(cats)
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Month"] + [c.replace("_", " ") for c in cats] +
                   ["TOTAL Accidents", "TOTAL Killed", "TOTAL Injured"])
        for mth in sorted(data, reverse=True):
            ns = [data[mth].get(c, (0, 0, 0))[0] for c in cats]
            w.writerow([mth] + ns + [sum(ns),
                                     sum(v[1] for v in data[mth].values()),
                                     sum(v[2] for v in data[mth].values())])
    return len(data)


STALE = ["SUMMARY.csv", "SUMMARY_simple.csv", "SUMMARY_month_by_type.csv", "SUMMARY_weekly.csv",
         "SUMMARY_by_city.csv", "SUMMARY_casualties_monthly.csv", "SUMMARY_cause_histogram.csv",
         "SUMMARY_others_by_sector.csv", "SUMMARY_cause_phrases.csv", "cause_summary.csv",
         "cause_trend_monthly.csv", "monthly_summary.csv", "yearly_summary.csv",
         "articles.csv", "EVENTS_unique.csv", "index.html"]


def clear_stale():
    import os
    gone = [n for n in STALE if os.path.exists(n)]
    for n in gone:
        try:
            os.remove(n)
        except OSError:
            pass
    if gone:
        print("[cleanup] removed obsolete files:", ", ".join(gone))


# ===========================================================================
# RUN
# ===========================================================================
def run():
    conn = sqlite3.connect(DB_PATH)
    init_db(conn)
    stats, tbudget = {}, MAX_TRANSLATE_PER_RUN

    for code, (label, ceid) in EDITIONS.items():
        for q in GN_QUERIES.get(code, []):
            url = f"{RSS_SEARCH}{urllib.parse.quote(q)}&hl={code}-IN&gl=IN&ceid={ceid}"
            data, _ = http_get(url)
            items = parse_feed(data, label, q)
            n, tbudget = store(conn, items, stats, tbudget)
            print(f"[GN {label}] {q!r}: {len(items)} seen, {n} kept")
            time.sleep(1)

    for label, url in NEWSPAPER_FEEDS:
        data, _ = http_get(url)
        if data is None:
            print(f"[PAPER {label}] unreachable: {url}")
            continue
        items = parse_feed(data, label, url)
        n, tbudget = store(conn, items, stats, tbudget)
        print(f"[PAPER {label}] {len(items)} seen, {n} kept")
        time.sleep(1)

    # Fetch article bodies FIRST, then screen and classify, so both decisions are
    # made on the full text rather than the headline alone.
    for name, fn in (("articles", lambda: backfill_articles(conn, MAX_ARTICLE_FETCH_PER_RUN)),
                     ("rescreen", lambda: rescreen_all(conn)),
                     ("dedupe", lambda: rededupe(conn))):
        try:
            fn()
        except Exception as e:                                      # noqa: BLE001
            print(f"[warn] {name} failed and was skipped: {type(e).__name__}: {e}")

    clear_stale()
    n = export_accidents(conn)
    export_summary(conn, "SUMMARY_all.csv", False)
    export_summary(conn, "SUMMARY_confirmed.csv", True)
    export_monthly(conn)
    conn.close()

    print(f"\nACCIDENTS.csv written: {n} unique accidents")
    print("Screening outcomes this run:")
    for k, v in sorted(stats.items(), key=lambda kv: -kv[1]):
        print(f"   {v:6}  {k}")


# ===========================================================================
# SELF TEST
# ===========================================================================
if __name__ == "__main__":
    if "--self-test" in sys.argv:
        drop = [
            ("bangladeshi outlet", "Bus accident kills 5 in Dhaka", "Prothom Alo"),
            ("bangladeshi outlet 2", "Steel factory blast injures 3 in Dhaka", "bd-pratidin.com"),
            ("alaska", "Plane crash in Alaska kills 10", "NDTV"),
            ("food safety", "Fungus found in food at Karnataka railway station", "The Hindu"),
            ("trekking", "Two trekkers die during trek in Himachal", "NDTV"),
            ("protest", "Transporters block road during student rally in Patna", "Jagran"),
            ("assault", "School student dies after assault by classmates in Delhi", "NDTV"),
            ("riot 1984", "1984 riots: victims remember the carnage in Delhi", "The Hindu"),
            ("murder", "Man murdered in Kanpur, body found", "Amar Ujala"),
            ("suicide", "Student ends life in Kota", "Dainik Bhaskar"),
            ("investigation", "AI-171 crash investigation: pilots demand hearing", "NDTV"),
            ("compensation", "Ex-gratia announced for road accident victims in Bihar", "Jagran"),
            ("statistic", "418 died in road accidents in one month across the country", "NDTV"),
            ("natural", "20 dead as floods hit Kerala", "The Hindu"),
            ("sport", "Cricket tournament begins in Mumbai", "Times of India"),
        ]
        for label, t, s in drop:
            keep, why = screen(t, "", s, "", "2026-08-20")
            assert not keep, f"{label} SHOULD BE DROPPED: {t}"

        keep_cases = [
            ("3 killed as bus overturns on NH-48 near Pune", "Dainik Bhaskar", "roadway"),
            ("Two policemen killed in collision between car and tanker in Shimla", "NDTV", "roadway"),
            ("Train derails near Kanpur, 4 dead", "Jagran", "train"),
            ("Under-construction flyover girder collapses in Hardoi, 2 injured", "Amar Ujala", "construction_ongoing"),
            ("Dilapidated building collapses in Bhiwandi, 3 dead", "Times of India", "old_structure_collapse"),
            ("Boat capsizes in Godavari near Rajahmundry, 6 missing", "Eenadu", "port_maritime"),
            ("Plane makes crash landing at Jaipur airport", "ABP Live", "aviation"),
            ("Boiler blast at chemical factory in Surat, 3 workers hurt", "Sandesh", "others"),
        ]
        for t, s, expect in keep_cases:
            keep, why = screen(t, "", s, "", "2026-08-20")
            assert keep, f"SHOULD BE KEPT (dropped as {why}): {t}"
            cat, _ = classify(t)
            assert cat == expect, f"{t!r} -> {cat}, expected {expect}"

        # Bengali-language INDIAN outlets must be accepted (a correction: these
        # were wrongly blocked as Bangladeshi in an earlier build)
        for outlet in ["Kolkata24x7", "najarbandi.in", "Anandabazar", "Ei Samay",
                       "Bartaman", "News18 Bangla", "TV9 Bangla"]:
            assert source_verdict(outlet) == "indian", f"{outlet} is Indian"
        for outlet in ["Prothom Alo", "bdnews24.com", "The Daily Star", "bd-pratidin.com"]:
            assert source_verdict(outlet) == "foreign", f"{outlet} is Bangladeshi"
        # Barjora is in Bankura, WEST BENGAL - an Indian accident
        keep, why = screen("Explosion in steel factory in Barjora, Bankura, 3 workers injured",
                           "", "Kolkata24x7", "", "2026-08-20")
        assert keep, f"Barjora/Bankura is in India but was dropped as {why}"

        # AVIATION must mean an aircraft, not merely the word "airport"
        for t, expect in [("Airport worker killed in road accident", "roadway"),
                          ("Bike collides with car on Nedumbassery Airport Road", "roadway"),
                          ("IAF transport plane crashes in Jorhat, 5 killed", "aviation")]:
            got, _ = classify(t)
            assert got == expect, f"aviation scope: {t!r} -> {got}, want {expect}"
        # a person's Indian origin does NOT place the event in India
        for t in ["Indian Origin Couple Killed In UK Plane Crash",
                  "Indian-origin pilot killed in helicopter crash in US",
                  "Indian Student and Pilot Killed in Essex Plane Crash",
                  "Pennsylvania crash: helicopter and Cessna collide midair"]:
            keep, _ = screen(t, "", "NDTV", "", "2026-08-20")
            assert not keep, f"foreign accident kept: {t}"
        # OTHERS must not swallow road and rail events
        assert classify("Kinnar dies after being hit by Vande Bharat")[0] == "train"
        assert classify("Student dies, search for vehicle that hit from behind")[0] == "roadway"
        assert classify("5 injured after Ferris wheel cabin crashes at Lucknow fair") == ("others", "amusement_ride")

        # CONSTRUCTION - full safety scope, and it must WIN over road/structure
        for t in ["Launching girder falls during metro construction on NH-24, 2 killed",
                  "Crane collapses at under-construction building in Noida",
                  "Worker falls from scaffolding at construction site in Pune",
                  "Labourer electrocuted while chipping at metro work site",
                  "Two workers buried as trench caves in during pipeline laying in Delhi",
                  "Painter falls from cradle at under-construction tower in Mumbai",
                  "Passerby killed as material falls from construction site in Bengaluru",
                  "Fire at under-construction metro station in Chennai",
                  "Worker struck by boom lift at bridge construction project in Patna"]:
            got, _ = classify(t)
            assert got == "construction_ongoing", f"construction scope: {t!r} -> {got}"
        # EXISTING STRUCTURE - including roads caving in and things falling onto people
        for t in ["Road caves in near Andheri, car falls into pit, 1 dead",
                  "Road settlement causes truck to overturn in Ghaziabad",
                  "Hoarding falls on vehicles in Mumbai, 2 killed",
                  "Old culvert gives way under truck near Nashik",
                  "Foot overbridge collapses at railway station in Delhi"]:
            got, _ = classify(t)
            assert got == "old_structure_collapse", f"structure scope: {t!r} -> {got}"
        # AVIATION needs a real aircraft event, and aftermath pieces are not events
        assert classify("Airport worker killed in road accident")[0] == "roadway"
        for t in ["How Ahmedabad Plane Crash Victim Changed His Family's Fate",
                  "Plane accident did not happen due to fuel switch",
                  "Air India plane crash: Relatives asked for black box data"]:
            keep, _ = screen(t, "", "NDTV", "", "2026-08-20")
            assert not keep, f"aviation aftermath kept: {t}"

        # the broadened construction vocabulary: activities, formwork, rebar
        for t in ["Worker dies while binding rebar at slab casting in Noida",
                  "Labourer falls during deshuttering of formwork at Pune site",
                  "Two hurt as shuttering collapses during concrete pour in Surat",
                  "Mason falls from staging while plastering in Lucknow",
                  "Worker electrocuted during wiring work at under-construction mall",
                  "Helper crushed by transit mixer at batching plant in Jaipur",
                  "Fall from cradle during facade cladding work in Gurugram",
                  "Worker dies during post-tensioning at bridge project in Bihar",
                  "Contractor's worker dies in fall from tower crane in Hyderabad"]:
            assert classify(t)[0] == "construction_ongoing", f"construction: {t!r}"
        # and it must NOT steal ordinary transport or structure events
        for t, e in [("3 killed as bus overturns on NH-48 near Pune", "roadway"),
                     ("Train derails near Kanpur, 4 dead", "train"),
                     ("Dilapidated building collapses in Bhiwandi", "old_structure_collapse"),
                     ("Road caves in near Andheri, 1 dead", "old_structure_collapse")]:
            assert classify(t)[0] == e, f"over-capture: {t!r} -> {classify(t)[0]}"
        # classification must be able to use the ARTICLE BODY, not just the title
        headline = "Worker dies in Noida"
        body = ("A 32-year-old labourer died after falling from the scaffolding of an "
                "under-construction tower in Sector 78 while plastering the seventh floor.")
        assert classify(headline)[0] != "construction_ongoing", "headline alone lacks evidence"
        assert classify(headline + " " + body)[0] == "construction_ongoing", \
            "the article body must drive classification"

        # regressions the user reported
        cat, _ = classify("Road accidents in UP; Mother and daughter killed in truck collision in Sambhal")
        assert cat == "roadway", f"row 57 regression: got {cat}"
        cat, _ = classify("Young woman dies in car accident in Guntur")
        assert cat == "roadway", f"row 74 regression: got {cat}"

        assert extract_counts("3 killed, 2 injured in bus crash on NH-48") == (3, 2)
        assert extract_counts("70-yr-old killed in road accident") == (None, None)
        assert extract_counts("70 sheep killed in train collision") == (None, None)
        assert extract_counts("9 Nationals Killed In Kolkata Hotel Fire") == (9, None)
        assert extract_time_of_day("crash at 12 am") == "Night"
        assert extract_time_of_day("crash at 12 pm") == "Day"

        # rows 112/117: same blast, different transliteration -> ONE accident
        conn = sqlite3.connect(":memory:")
        init_db(conn)
        st = {}
        ts = datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()
        for t, src in [("Explosion in steel factory in Bankura, 3 workers injured by molten iron", "Anandabazar"),
                       ("Blast in the steel factory in Bankura, 3 workers burnt", "Ei Samay")]:
            store(conn, [{"title": t, "snippet": "", "url": "http://x/" + t[:8], "source": src,
                          "language": "English", "query": "q", "published": "2026-08-20",
                          "published_ts": ts}], st)
        rededupe(conn)
        uniq = conn.execute("SELECT COUNT(*) FROM articles WHERE is_duplicate=0").fetchone()[0]
        print(f"steel factory blast: 2 reports -> {uniq} accident(s)")
        assert uniq == 1, "the two reports of one blast should merge"
        print("SELF-TEST PASSED")
    else:
        run()
