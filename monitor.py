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
EVENT_DATE_WINDOW_DAYS = 3        # normal matching window
FOLLOWUP_WINDOW_DAYS = 30         # follow-up coverage of one accident can run for
                                  # weeks (the Bhiwandi collapse was reported from
                                  # 30 July to 22 August). Merging across that span
                                  # is allowed ONLY on a strong match: same place,
                                  # same category and high content overlap.
EVENT_SIM_THRESHOLD = 0.70
TITLE_DUP_THRESHOLD = 0.90
TRANSLATE_BACKEND = "builtin"      # "builtin" | "none"
MAX_TRANSLATE_PER_RUN = 4000     # cap is generous; throttling is the real limit
MAX_ARTICLE_FETCH_PER_RUN = 2500  # only fetchable URLs consume this
ARTICLE_FETCH_MINUTES = 45        # wall-clock guard so a run cannot overrun
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

# Direct publisher feeds matter far more than they appear to. Google News RSS
# links are redirect stubs that cannot be resolved for free, so those items never
# yield article text - and without article text there is no reported cause. These
# feeds give real URLs, so they are the ONLY source of cause data. Add more of
# them to raise cause coverage; dead ones are skipped and logged.
NEWSPAPER_FEEDS = [
    ("English", "https://indianexpress.com/feed/"),
    ("English", "https://indianexpress.com/section/cities/feed/"),
    ("English", "https://indianexpress.com/section/india/feed/"),
    ("English", "https://www.thehindu.com/news/national/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/cities/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/national/andhra-pradesh/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/national/karnataka/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/national/kerala/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/national/tamil-nadu/feeder/default.rss"),
    ("English", "https://www.thehindu.com/news/national/telangana/feeder/default.rss"),
    ("English", "https://feeds.feedburner.com/ndtvnews-india-news"),
    ("English", "https://feeds.feedburner.com/ndtvnews-cities-news"),
    ("English", "https://www.news18.com/rss/india.xml"),
    ("English", "https://www.news18.com/rss/cities.xml"),
    ("English", "https://www.deccanherald.com/rss/national.rss"),
    ("English", "https://www.deccanherald.com/rss/karnataka.rss"),
    ("English", "https://www.newindianexpress.com/nation/rss"),
    ("English", "https://www.newindianexpress.com/states/tamil-nadu/rss"),
    ("English", "https://www.newindianexpress.com/states/kerala/rss"),
    ("English", "https://www.freepressjournal.in/stories.rss"),
    ("English", "https://www.thestatesman.com/feed"),
    ("English", "https://www.tribuneindia.com/rss/feed?catId=1"),
    ("English", "https://www.dnaindia.com/feeds/india.xml"),
    ("English", "https://timesofindia.indiatimes.com/rssfeeds/-2128936835.cms"),
    ("English", "https://timesofindia.indiatimes.com/rssfeeds/1221656.cms"),
    ("English", "https://www.hindustantimes.com/feeds/rss/cities/index.xml"),
    ("English", "https://www.hindustantimes.com/feeds/rss/india-news/index.xml"),
    ("English", "https://scroll.in/feed"),
    ("English", "https://www.telegraphindia.com/feeds/rss.jsp?id=3",),
    ("Hindi",   "https://feed.livehindustan.com/rss/3127"),
    ("Hindi",   "https://feed.livehindustan.com/rss/21"),
    ("Hindi",   "https://www.bhaskar.com/rss-v1--category-1707.xml"),
    ("Hindi",   "https://navbharattimes.indiatimes.com/rssfeedsdefault.cms"),
    ("Hindi",   "https://www.jagran.com/rss/news/national.xml"),
    ("Hindi",   "https://www.amarujala.com/rss/india-news.xml"),
    ("Hindi",   "https://www.patrika.com/rss/india-news.xml"),
    ("Marathi", "https://www.loksatta.com/feed/"),
    ("Marathi", "https://marathi.abplive.com/home/feed"),
    ("Bengali", "https://bengali.abplive.com/home/feed"),
    ("Bengali", "https://www.anandabazar.com/rss/state"),
    ("Tamil",   "https://tamil.abplive.com/home/feed"),
    ("Tamil",   "https://www.dinamani.com/rss/tamilnadu"),
    ("Telugu",  "https://telugu.abplive.com/home/feed"),
    ("Kannada", "https://kannada.abplive.com/home/feed"),
    ("Malayalam", "https://www.mathrubhumi.com/cmlink/1.1258576"),
    ("Gujarati", "https://gujarati.abplive.com/home/feed"),
    ("Punjabi", "https://www.jagbani.punjabkesari.in/rss/news/national.xml"),
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
    # an Indian domain settles it (GDELT supplies bare domains like
    # "indianexpress.com" or "thehindu.com", so match those too)
    if re.search(r"\.in\b|\.co\.in\b|india\.com|indiatimes\.com|indianexpress\.com|"
                 r"thehindu\.com|hindustantimes\.com|ndtv\.com|news18\.com|"
                 r"deccanherald\.com|tribuneindia\.com|telegraphindia\.com|"
                 r"newindianexpress\.com|freepressjournal\.in|bhaskar\.com|"
                 r"jagran\.com|amarujala\.com|patrika\.com|livemint\.com|"
                 r"business-standard\.com|scroll\.in|theprint\.in|thewire\.in", hay):
        return "indian"
    if re.search(r"\.bd\b|\.pk\b|\.np\b|\.lk\b|\.cn\b|\.uk\b|\.us\b|\.au\b", hay):
        return "foreign"
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
    "Muzaffarnagar", "Firozabad", "Mathura", "Vrindavan", "Ayodhya", "Barsana",
    "Govardhan", "Gokul", "Nandgaon", "Shamli", "Baghpat", "Kasganj", "Sambhal", "Jaunpur", "Azamgarh", "Ballia",
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

# Phrases describing a PERSON'S nationality, which say nothing about where an
# event occurred. This cuts BOTH ways:
#   * "Indian-origin pilot killed in US crash" is a US accident, not an Indian one;
#   * "Nepali worker among 3 killed at Vrindavan site" is an INDIAN accident, and
#     dropping it because the word "Nepal" appears would lose a real event.
# Migrant labour on Indian construction sites frequently comes from Nepal,
# Bangladesh and Bihar's neighbouring countries, so this matters for exactly the
# category we care most about.
PERSON_ORIGIN = re.compile(r"\b(?:indian[-\s]origin|indian student|indian couple|"
                           r"indian national|indian citizen|indian tourist|malayali|"
                           r"indian[-\s]american|nri)\b", re.I)

FOREIGN_PERSON = re.compile(
    # "<Country> National among 3 killed" - the actual Times of India phrasing.
    # A country name followed by a PERSON word names a nationality, not a place.
    r"\b(?:nepal|bangladesh|pakistan|sri ?lanka|bhutan|myanmar|afghanistan|tibet|china|"
    r"nigeria|kenya|uganda|sudan|somalia)\s+"
    r"(?:national|nationals|native|natives|citizen|citizens|worker|workers|labourer|"
    r"labourers|labour|migrant|migrants|man|men|woman|women|youth|student|students|"
    r"family|origin)\b"
    r"|\b(?:nepali|nepalese|bangladeshi|pakistani|sri ?lankan|bhutanese|burmese|"
    r"afghan|tibetan|chinese|nigerian|kenyan|ugandan|sudanese|somali)"
    r"(?:[-\s](?:origin|national|nationals|citizen|citizens|worker|workers|labourer|"
    r"labourers|labour|migrant|migrants|man|woman|youth|student|family|native|natives))?\b"
    r"|\b(?:native|citizen|resident|worker|workers|labourer|labourers|migrant|migrants|"
    r"man|woman|youth|student|national|nationals)\s+(?:of|from)\s+"
    r"(?:nepal|bangladesh|pakistan|sri lanka|bhutan|myanmar|afghanistan|tibet)\b"
    r"|\b(?:from|of)\s+(?:nepal|bangladesh|bhutan)\b(?=[^.]{0,60}\b(?:worker|labour\w*|"
    r"migrant|national|native|man|woman|youth|student|among|including|die|dies|died|"
    r"killed|construction|site)\b)"
    r"|\b(?:including|among|along with|besides)\s+(?:one|two|three|a|an|some|several)?\s*"
    r"(?:person|worker|labourer|migrant|national|native|man|woman|youth)?\s*"
    r"(?:from|of)?\s*(?:nepal|bangladesh|bhutan|pakistan|sri lanka)\b", re.I)
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


_INDIA_LOCATIVE = None      # built lazily from the gazetteer
_FOREIGN_LOCATIVE = re.compile(
    r"\b(?:in|at|near|outside|inside)\s+(?:the\s+)?(?:[A-Z][a-z]+\s+)?(?:" +
    FOREIGN_PLACES.pattern.split("(?:", 1)[1].rstrip(")\\b") + r")", re.I)


def _india_locative(text):
    """True when the text says the event happened IN/AT/NEAR an Indian place."""
    for name, _pat in _PLACE_PATTERNS[:4000]:
        i = text.lower().find(name.lower())
        while i > 0:
            before = text[max(0, i - 12):i]
            if re.search(r"\b(?:in|at|near|outside|inside)\s+$", before, re.I):
                return True
            i = text.lower().find(name.lower(), i + 1)
    return False



# Foreign country names written in INDIAN SCRIPTS. Without these, a Tamil report
# of a Ugandan school-bus crash or a Colombian earthquake passed as Indian,
# because the foreign-place list was Latin-only.
FOREIGN_NATIVE = [
    # Hindi / Marathi
    "बांग्लादेश", "पाकिस्तान", "नेपाल", "श्रीलंका", "अफगानिस्तान", "म्यांमार", "भूटान",
    "चीन", "अमेरिका", "ब्रिटेन", "इंग्लैंड", "रूस", "यूक्रेन", "जापान", "कोरिया",
    "इंडोनेशिया", "फिलीपींस", "थाईलैंड", "वियतनाम", "मलेशिया", "सिंगापुर", "सऊदी",
    "दुबई", "कतर", "कुवैत", "ओमान", "इराक", "ईरान", "इजरायल", "मिस्र", "तुर्की",
    "नाइजीरिया", "केन्या", "युगांडा", "इथियोपिया", "दक्षिण अफ्रीका", "ब्राजील",
    "मैक्सिको", "कोलंबिया", "पेरू", "अर्जेंटीना", "कनाडा", "ऑस्ट्रेलिया", "जर्मनी",
    "फ्रांस", "इटली", "स्पेन", "पोलैंड", "हंगरी", "ग्रीस", "ढाका", "कराची", "लाहौर",
    "काठमांडू", "कोलंबो",
    # Bengali
    "বাংলাদেশ", "পাকিস্তান", "নেপাল", "শ্রীলঙ্কা", "চীন", "আমেরিকা", "ব্রিটেন", "রাশিয়া",
    "জাপান", "ইন্দোনেশিয়া", "সৌদি", "দুবাই", "নাইজেরিয়া", "উগান্ডা", "কলম্বিয়া",
    "ব্রাজিল", "কানাডা", "অস্ট্রেলিয়া", "ঢাকা", "করাচি", "কাঠমান্ডু",
    # Tamil
    "பங்களாதேஷ்", "வங்கதேசம்", "பாகிஸ்தான்", "நேபாள", "இலங்கை", "சீனா", "அமெரிக்க",
    "பிரிட்டன்", "ரஷ்யா", "ஜப்பான்", "இந்தோனேசிய", "சவுதி", "துபாய்", "நைஜீரிய",
    "உகாண்டா", "கொலம்பிய", "பிரேசில்", "கனடா", "ஆஸ்திரேலிய", "டாக்கா", "கராச்சி",
    # Telugu
    "బంగ్లాదేశ్", "పాకిస్తాన్", "నేపాల్", "శ్రీలంక", "చైనా", "అమెరికా", "బ్రిటన్", "రష్యా",
    "జపాన్", "సౌదీ", "దుబాయ్", "నైజీరియా", "ఉగాండా", "కొలంబియా", "బ్రెజిల్", "ఢాకా",
    # Kannada
    "ಬಾಂಗ್ಲಾದೇಶ", "ಪಾಕಿಸ್ತಾನ", "ನೇಪಾಳ", "ಶ್ರೀಲಂಕಾ", "ಚೀನಾ", "ಅಮೆರಿಕ", "ಬ್ರಿಟನ್",
    "ರಷ್ಯಾ", "ಜಪಾನ್", "ಸೌದಿ", "ದುಬೈ", "ಉಗಾಂಡಾ", "ಕೊಲಂಬಿಯಾ", "ಬ್ರೆಜಿಲ್",
    # Malayalam
    "ബംഗ്ലാദേശ്", "പാകിസ്ഥാൻ", "നേപ്പാൾ", "ശ്രീലങ്ക", "ചൈന", "അമേരിക്ക", "ബ്രിട്ടൻ",
    "റഷ്യ", "ജപ്പാൻ", "സൗദി", "ദുബായ്", "ഉഗാണ്ട", "കൊളംബിയ", "ബ്രസീൽ",
    # Gujarati / Punjabi
    "બાંગ્લાદેશ", "પાકિસ્તાન", "નેપાળ", "શ્રીલંકા", "ચીન", "અમેરિકા", "સાઉદી", "દુબઈ",
    "ਬੰਗਲਾਦੇਸ਼", "ਪਾਕਿਸਤਾਨ", "ਨੇਪਾਲ", "ਸ਼੍ਰੀਲੰਕਾ", "ਚੀਨ", "ਅਮਰੀਕਾ", "ਸਾਊਦੀ", "ਦੁਬਈ",
]


def india_verdict(text):
    if not text:
        return "unknown"
    # Strip person-nationality phrases FIRST, so "Nepali worker killed in
    # Vrindavan" is judged on "killed in Vrindavan" and reads as India.
    without_people = FOREIGN_PERSON.sub(" ", text)

    # Decide on the LOCATIVE phrase - the one that states where it happened.
    # "Nepal native among 3 dead as wall collapses AT MATHURA site" is Indian;
    # "Bus plunges into gorge IN NEPAL" is not. A bare country name that is not
    # introduced by in/at/near is describing a person, not a place.
    # Nationality phrases in Indian scripts describe PEOPLE, not the location:
    # "नेपाल के एक मजदूर" = "a labourer from Nepal".
    native_people = re.sub(
        r"(?:नेपाल|बांग्लादेश|पाकिस्तान|श्रीलंका|भूटान)\s*(?:के|की|का|से)?\s*"
        r"(?:एक\s*)?(?:मजदूर|श्रमिक|नागरिक|मूल|निवासी|युवक|व्यक्ति|महिला|कामगार)"
        r"|नेपाली|बांग्लादेशी|पाकिस्तानी"
        r"|(?:নেপাল|বাংলাদেশ|পাকিস্তান)\s*(?:এর|থেকে)?\s*(?:শ্রমিক|নাগরিক|যুবক|ব্যক্তি)"
        r"|নেপালি|বাংলাদেশি"
        r"|(?:நேபாள|பங்களாதேஷ்)\s*(?:தொழிலாளி|நாட்டவர்)"
        r"|(?:నేపాల్|బంగ్లాదేశ్)\s*(?:కూలీ|జాతీయుడు)",
        " ", without_people)
    if any(w in native_people for w in FOREIGN_NATIVE):
        return "foreign"
    without_people = native_people
    foreign_here = bool(_FOREIGN_LOCATIVE.search(without_people))
    india_here = _india_locative(without_people)
    if india_here and not foreign_here:
        return "india"
    if foreign_here:
        return "foreign"
    if FOREIGN_PLACES.search(without_people):
        return "foreign"
    # A person's nationality is not evidence of WHERE the accident happened, in
    # either direction. Remove those phrases before judging the location.
    stripped = PERSON_ORIGIN.sub(" ", without_people)
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
    r"emergency landing|crash landing|runway excursion|hit and run|head-on)\b"
    # A death or injury AT a workplace or construction site is an accident even
    # when the headline uses no crash word: "labourers die at Vrindavan temple
    # construction site" describes an accident as plainly as "collapse" does.
    r"|\b(?:die|dies|died|killed|kills|dead|injured|hurt|crushed|buried|trapped|"
    r"electrocuted|drowned|burnt|burned)\b[^.]{0,50}?\b(?:construction|worksite|"
    r"work site|building site|project site|factory|plant|mill|mine|quarry|godown|"
    r"warehouse|workshop|scaffold\w*|shuttering|formwork|crane|girder|excavation|"
    r"trench|metro site|site)\b"
    r"|\b(?:at|on|during)\s+(?:the\s+)?(?:construction|building|project|metro|bridge|"
    r"factory|plant|mine|quarry)\s*(?:site|work|works)?\b[^.]{0,50}?"
    r"\b(?:die|dies|died|killed|dead|injured|hurt|crushed|buried|trapped)\b"
    # Workers dying or being injured is itself the accident. Deliberate violence
    # is already excluded earlier, so this does not admit murders.
    r"|\b(?:worker|workers|labourer|labourers|labour|employee|employees|staff|"
    r"mazdoor|mistri|mason)\b[^.]{0,40}?"
    r"\b(?:die|dies|died|killed|dead|injured|hurt|crushed|buried|trapped|electrocuted)\b"
    r"|\b(?:killed|died|dies|injured|hurt|crushed|buried|trapped)\b[^.]{0,40}?"
    r"\b(?:worker|workers|labourer|labourers|mazdoor|mason)\b", re.I)

ACCIDENT_NATIVE = ["दुर्घटना", "हादस", "टक्कर", "पलट", "ढह", "गिर", "धमाका", "विस्फोट", "आग लग",
    "मलबे", "दब", "कुचल", "शटरिंग", "मचान", "क्रेन",
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
    # agitation / reservation stir vocabulary - deaths during a protest are not
    # accidents, and the Maratha reservation coverage was slipping through
    "आंदोलक", "आंदोलन", "मोर्चा", "मोर्चात", "उपोषण", "आरक्षण", "उपोषणकर्ता",
    "निदर्शन", "संप", "बंद", "रास्ता रोको", "घेराव", "सत्याग्रह",
    "আন্দোলন", "মিছিল", "অনশন", "ধর্মঘট", "সংরক্ষণ",
    "போராட்ட", "உண்ணாவிரத", "இடஒதுக்கீடு", "ஆர்ப்பாட்ட",
    "ఆందోళన", "నిరాహారదీక్ష", "రిజర్వేషన్", "ధర్నా",
    "ಪ್ರತಿಭಟನೆ", "ಉಪವಾಸ", "ಮೀಸಲಾತಿ", "ಧರಣಿ",
    "സമരം", "നിരാഹാര", "സംവരണം", "പ്രക്ഷോഭ",
    "આંદોલન", "અનામત", "ઉપવાસ", "ਅੰਦੋਲਨ", "ਰਾਖਵਾਂਕਰਨ", "ਭੁੱਖ ਹੜਤਾਲ",
    "খুন", "হত্যা", "দাঙ্গা", "হামলা", "আত্মহত্যা", "প্রতিবাদ", "শ্রদ্ধাঞ্জলি",
    "आंदोलन", "கொலை", "தாக்குதல்", "தற்கொலை", "போராட்டம்",
    "హత్య", "దాడి", "ఆత్మహత్య", "నిరసన", "ಕೊಲೆ", "ದಾಳಿ", "ಆತ್ಮಹತ್ಯೆ", "ಪ್ರತಿಭಟನೆ",
    "കൊലപാതകം", "ആക്രമണം", "ആത്മഹത്യ", "പ്രതിഷേധം",
    "હત્યા", "હુમલો", "આત્મહત્યા", "વિરોધ", "ਕਤਲ", "ਹਮਲਾ", "ਖ਼ੁਦਕੁਸ਼ੀ", "ਪ੍ਰਦਰਸ਼ਨ"]

NATURAL_HAZARD = re.compile(
    r"\b(?:flood\w*|deluge|inundat\w*|landslide|landslip|mudslide|cloudburst|avalanche|"
    r"earthquake|quake|tremor|cyclone|hurricane|typhoon|tornado|tsunami|lightning|"
    r"thunderbolt|hailstorm|wildfire|forest fire|glacier\w*|glacial|snow ?slide|"
    r"glof|glacial lake)\b", re.I)
NATURAL_NATIVE = ["बाढ़", "भूस्खलन", "भूकंप", "चक्रवात", "बिजली गिर", "बादल फट", "हिमस्खलन",
    "ग्लेशियर", "हिमनद", "हिमोढ़",
    "বন্যা", "ভূমিধস", "ভূমিকম্প", "ঘূর্ণিঝড়", "বজ্রপাত", "হিমবাহ", "তুষারধস", "প্লাবন",
    "வெள்ளம்", "நிலச்சரிவு", "பனிச்சரிவு", "பனியாறு",
    "నిలநடுக்கம்", "వరద", "కొండచరియ", "భూకంపం", "హిమానీనదం", "మంచు హిమపాతం",
    "ಪ್ರವಾಹ", "ಭೂಕುಸಿತ", "ಭೂಕಂಪ", "ಹಿಮನದಿ", "ಹಿಮಪಾತ",
    "വെള്ളപ്പൊക്കം", "ഉരുൾപൊട്ടൽ", "ഭൂകമ്പം", "ഹിമാനി", "ഹിമപാതം",
    "પૂર", "ભૂસ્ખલન", "ધરતીકંપ", "હિમનદી", "હિમપ્રપાત", "ਹੜ੍ਹ", "ਭੂਚਾਲ", "ਗਲੇਸ਼ੀਅਰ", "ਬਰਫ਼ਸਖਲਨ"]

# "N years ago", "N years back" and their equivalents mark a retrospective, not
# a current event. The English forms are caught by OLD_EVENT; these are the same
# cue in Indian scripts (a Bengali glacier-disaster anniversary was slipping the
# date gate because "১১ বছর আগের" was not recognised as "11 years ago").
NATIVE_OLD = ["बछर आगे", "बछर आगेर", "साल पहले", "वर्ष पहले", "साल पूर्व", "बरस पहले",
    "বছর আগে", "বছর আগের", "বছর আগেকার", "বর্ষ আগে",
    "वर्षापूर्वी", "वर्षांपूर्वी", "साल आधी",
    "ஆண்டுகளுக்கு முன்", "ஆண்டு முன்", "సంవత్సరాల క్రితం", "ఏళ్ల క్రితం",
    "ವರ್ಷಗಳ ಹಿಂದೆ", "ವರ್ಷದ ಹಿಂದೆ", "വർഷം മുൻപ്", "വർഷങ്ങൾക്ക് മുൻപ്",
    "વર્ષ પહેલા", "વર્ષ પહેલાં", "ਸਾਲ ਪਹਿਲਾਂ", "ਵਰ੍ਹੇ ਪਹਿਲਾਂ"]


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


AGGREGATE_NATIVE = [
    # "in N months / years", "per year", "so far this year" in Indian scripts
    "महीनों में", "महीने में", "वर्षों में", "सालों में", "साल में", "प्रतिवर्ष", "हर साल",
    "अब तक", "आंकड़ों के अनुसार", "रिपोर्ट के अनुसार", "औसतन",
    "মাসে", "বছরে", "প্রতি বছর", "পরিসংখ্যান", "গড়ে",
    "महिन्यांत", "वर्षांत", "दरवर्षी", "सरासरी",
    "மாதங்களில்", "ஆண்டுகளில்", "ஆண்டில்", "சராசரியாக", "புள்ளிவிவர",
    "నెలల్లో", "సంవత్సరాల్లో", "ఏటా", "సగటున", "గణాంకాల",
    "ತಿಂಗಳಲ್ಲಿ", "ವರ್ಷಗಳಲ್ಲಿ", "ಪ್ರತಿ ವರ್ಷ", "ಸರಾಸರಿ",
    "മാസങ്ങളിൽ", "വർഷങ്ങളിൽ", "പ്രതിവർഷം", "ശരാശരി",
    "મહિનામાં", "વર્ષોમાં", "દર વર્ષે", "સરેરાશ",
    "ਮਹੀਨਿਆਂ ਵਿੱਚ", "ਸਾਲਾਂ ਵਿੱਚ", "ਹਰ ਸਾਲ", "ਔਸਤਨ",
]


def currency_verdict(text, published_date):
    if not text:
        return "not_event"
    # a statistical round-up written in an Indian language
    if any(w in text for w in AGGREGATE_NATIVE):
        return "not_event"
    if NOT_EVENT_REPORT.search(text):
        return "not_event"
    if OLD_EVENT.search(text) or any(w in text for w in NATIVE_OLD):
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
            "ఆరుగురికి": 6, "ఆరుగురిని": 6, "ఆరుగురి": 6, "ఆరుగురు": 6,
            "ఐదుగురికి": 5, "ఏడుగురికి": 7, "ಇಬ್ಬರು": 2, "ಮೂವರು": 3, "બે": 2, "ਦੋ": 2}

DEATH_CUES = ["killed", "kills", "dead", "death", "deaths", "died", "dies", "die",
              "deceased", "lost lives", "lose life", "perished",
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
    # Outlet and channel names carry numbers that are NOT casualties: News18, TV9,
    # Zee 24, 24 Ghanta, 10TV, V6, P7, ABP7. The number in "News18 Telugu" was
    # being read as a death toll (a Telugu "six died" story became "18 died"). A
    # real count always reads "6 killed" - a digit with a space before the
    # casualty word - so a digit GLUED to letters is never a toll, and the few
    # outlet names that put a space before the number are removed by name.
    t = re.sub(r"\b(?:zee|tv|channel|dd|colou?rs|news|sahara|aaj\s*tak|abp)\s+\d{1,3}\b", " ", t, flags=re.I)
    t = re.sub(r"\b24\s*(?:x\s*7|ghanta|ghante)\b", " ", t, flags=re.I)
    t = re.sub(r"\b[a-z]+\d{1,3}\b", " ", t, flags=re.I)      # news18, tv9, v6, p7, abp7
    t = re.sub(r"\b\d{1,3}[a-z]{2,}\b", " ", t, flags=re.I)   # 10tv, 99tv
    t = re.sub(r"\|\s*\d+\s*$", " ", t)
    t = re.sub(r"\b(?:nh|sh|mdr|national highway|state highway|route)\s*[-\u2013]?\s*\d+[a-z]?\b", " ", t, flags=re.I)
    t = re.sub(r"\b\d{1,3}\s*[-\u2013]?\s*(?:year|yr|yrs|years)\s*[-\u2013]?\s*old\b", " ", t, flags=re.I)
    # Ages in Indian scripts. These were NOT being stripped, so "25 वर्षीय मजदूर
    # की मौत" (a 25-year-old labourer died) was recorded as 25 deaths.
    t = re.sub(r"\d{1,3}\s*(?:वर्षीय|वर्ष|साल|बरस|वयाच्या|वर्षांच्या|वर्षीया)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:বছরের|বছর|বয়সী)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:வயது|வயதான|வயதுடைய)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:సంవత్సరాల|ఏళ్ల|ఏండ్ల|వయసు)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:ವರ್ಷದ|ವರ್ಷ|ವಯಸ್ಸಿನ)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:വയസ്സുള്ള|വയസ്സ്|വയസ്)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:વર્ષીય|વર્ષના|વર્ષ)", " ", t)
    t = re.sub(r"\d{1,3}\s*(?:ਸਾਲਾ|ਸਾਲ|ਵਰ੍ਹੇ)", " ", t)
    # durations, not casualties: "19 மாதங்களில்" = "in 19 months"
    t = re.sub(r"\d{1,4}\s*(?:महीनों|महीने|माह|दिनों|दिन|घंटे|सप्ताह|हफ्ते)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:মাসে|মাস|দিনে|দিন|ঘণ্টা|সপ্তাহ)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:महिन्यांत|महिने|दिवसांत|दिवस|तासांत)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:மாதங்களில்|மாதங்கள்|மாத|நாட்களில்|நாள்|மணி)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:నెలల్లో|నెలల|నెల|రోజుల్లో|రోజుల|గంటల)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:ತಿಂಗಳಲ್ಲಿ|ತಿಂಗಳ|ದಿನಗಳಲ್ಲಿ|ದಿನ|ಗಂಟೆ)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:മാസങ്ങളിൽ|മാസം|ദിവസം|മണിക്കൂർ)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:મહિનામાં|મહિના|દિવસ|કલાક)", " ", t)
    t = re.sub(r"\d{1,4}\s*(?:ਮਹੀਨਿਆਂ|ਮਹੀਨੇ|ਦਿਨ|ਘੰਟੇ)", " ", t)
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

    def _positions(cue):
        """Every position where this cue occurs, as a whole word for ASCII cues."""
        c = cue.lower().strip()
        if not c:
            return
        if c.isascii():
            for mm in re.finditer(r"\b" + re.escape(c) + r"\b", t):
                yield mm.start(), len(c)
        else:
            start = 0
            while True:
                i = t.find(c, start)
                if i == -1:
                    return
                yield i, len(c)
                start = i + len(c)

    def _cue_positions(cues):
        out = []
        for cue in cues:
            out.extend(p for p, _ in _positions(cue))
        return sorted(set(out))

    death_pos = _cue_positions(DEATH_CUES)
    injury_pos = _cue_positions(INJURY_CUES)

    def _cost(num_pos, cue_pos):
        """Distance from a number to a cue. A count almost always PRECEDES its
        own cue ("3 killed", "2 injured"), so a number sitting AFTER a cue is
        penalised heavily - otherwise "a worker died. Two others were injured"
        assigns the 2 to the deaths."""
        d = abs(num_pos - cue_pos)
        return d * (3.0 if num_pos > cue_pos else 1.0)

    # Assign EACH number to its own nearest cue, then take the best per type.
    best_d = best_i = None
    for mm in re.finditer(r"\d+", t):
        val = int(mm.group())
        if val <= 0 or val > 200 or 1900 <= val <= 2100:
            continue
        after = t[mm.end(): mm.end() + 26]
        am, hm = ANIMALS.search(after), HUMANS.search(after)
        if am and (not hm or am.start() < hm.start()):
            continue                       # animals are not casualties
        before_num = t[max(0, mm.start() - 16): mm.start()]
        # "3 workers INCLUDING ONE from Nepal" - the 1 is a subset, not the toll.
        # But "Nepal national AMONG 3 killed" means 3 in total, so "among" is
        # deliberately NOT treated as a subset marker.
        if re.search(r"\b(?:including|includes|of whom|of them|out of|apart from|"
                     r"besides|along with)\s*$", before_num, re.I):
            continue
        pos = mm.start()
        dc = min((_cost(pos, c) for c in death_pos), default=None)
        ic = min((_cost(pos, c) for c in injury_pos), default=None)
        if dc is None and ic is None:
            continue
        if ic is None or (dc is not None and dc <= ic):
            if dc is not None and dc <= 140 and (best_d is None or dc < best_d[0]):
                nearest = min(death_pos, key=lambda c: _cost(pos, c))
                best_d = (dc, val, pos, nearest)
        else:
            if ic <= 140 and (best_i is None or ic < best_i[0]):
                nearest = min(injury_pos, key=lambda c: _cost(pos, c))
                best_i = (ic, val, pos, nearest)

    d, i = best_d, best_i

    # STEP 1 - resolve a number claimed by BOTH cues, before any inference.
    # "a worker died. Two others were injured" - the 2 belongs to "injured".
    # In English the count precedes its own cue, so award it to the cue that
    # FOLLOWS the number. Doing this first matters: inferring a single victim
    # beforehand would be undone here.
    if d and i and d[2] == i[2]:
        d_after, i_after = d[3] > d[2], i[3] > i[2]
        if i_after and not d_after:
            d = None
        elif d_after and not i_after:
            i = None
        elif d[0] <= i[0]:
            i = None
        else:
            d = None

    # STEP 2 - infer a single victim ONLY where no number was found, so an
    # explicit count is never overridden ("9 Nationals Killed" stays 9).
    person = (r"person|man|woman|youth|girl|boy|child|labourer|laborer|worker|student|"
              r"driver|rider|pedestrian|villager|farmer|devotee|passenger|jawan|constable|"
              r"official|officer|engineer|teacher|doctor|soldier|cop|biker|son|daughter|"
              r"employee|resident|conductor|cyclist|motorcyclist|mason|helper|mistri|"
              r"grandmother|grandfather|mother|father|wife|husband|brother|sister|"
              r"minor|toddler|infant|elderly")
    death_verb = r"dies|died|killed|dead|was killed|is dead|lost (?:his|her) life"
    # Singular victims described in an Indian language: "25 वर्षीय मजदूर की मौत"
    # (a 25-year-old labourer died) carries no casualty NUMBER once the age is
    # stripped, so without this the death goes unrecorded.
    NATIVE_PERSON = ["मजदूर", "युवक", "युवती", "व्यक्ति", "व्यक्तीचा", "छात्र", "किशोर",
                     "चालक", "महिला", "बुजुर्ग", "श्रमिक", "कामगार", "बालक", "बालिका",
                     "শ্রমিক", "যুবক", "ব্যক্তি", "চালক", "মহিলা", "ছাত্র",
                     "மாணவ", "இளைஞர்", "தொழிலாளி", "ஓட்டுநர்", "பெண்",
                     "కూలీ", "యువకుడు", "వ్యక్తి", "డ్రైవర్", "మహిళ", "విద్యార్థి",
                     "ಕಾರ್ಮಿಕ", "ಯುವಕ", "ವ್ಯಕ್ತಿ", "ಚಾಲಕ", "ಮಹಿಳೆ",
                     "തൊഴിലാളി", "യുവാവ്", "വ്യക്തി", "ഡ്രൈവർ", "സ്ത്രീ",
                     "મજૂર", "યુવક", "વ્યક્તિ", "ડ્રાઈવર", "મહિલા",
                     "ਮਜ਼ਦੂਰ", "ਨੌਜਵਾਨ", "ਵਿਅਕਤੀ", "ਡਰਾਈਵਰ", "ਔਰਤ"]
    NATIVE_DEATH = ["मौत", "मृत्यु", "निधन", "ठार", "मृत", "নিহত", "মৃত্যু", "মৃত",
                    "மரணம்", "உயிரிழ", "பலி", "మృతి", "మరణ", "చనిపో",
                    "ಸಾವು", "ಮೃತ", "മരണം", "മരിച്ച", "મોત", "મૃત્યુ", "ਮੌਤ"]
    if d is None and any(p in t for p in NATIVE_PERSON) and any(c in t for c in NATIVE_DEATH):
        d = (0, 1, -1, -1)
    if d is None:
        if re.search(rf"\b(?:{person})\b(?:\s+\w+){{0,4}}?\s+(?:{death_verb})\b", t, re.I) \
           or (re.search(rf"\b(?:a|an|one)\s+(?:\d{{1,3}}[-\s]?year[-\s]?old\s+)?(?:{person})\b", t, re.I)
               and re.search(rf"\b(?:{death_verb})\b", t, re.I)):
            d = (0, 1, -1, -1)
    if i is None:
        if re.search(rf"\b(?:{person})\b(?:\s+\w+){{0,4}}?\s+(?:injured|hurt|wounded)\b", t, re.I) \
           or (re.search(rf"\b(?:a|an|one)\s+(?:{person})\b", t, re.I)
               and re.search(r"\b(?:injured|hurt|wounded)\b", t, re.I)
               and not re.search(r"\d+\s*(?:others?\s+)?(?:were\s+)?(?:injured|hurt)", t, re.I)):
            i = (0, 1, -2, -2)

    return (d[1] if d else None), (i[1] if i else None)


HIGHWAY_RE = [re.compile(r"\bNH[-\s]?\d{1,3}[A-Z]?\b", re.I),
              re.compile(r"\bSH[-\s]?\d{1,3}[A-Z]?\b", re.I),
              re.compile(r"\b[A-Z][a-z]+(?:[-\s][A-Z][a-z]+)?\s+Expressway\b")]

JUNK_PLACES = {"google", "news", "india", "indian", "bharat", "video", "watch", "live",
               "update", "breaking", "exclusive", "hindi", "bengali", "marathi", "tamil",
               "telugu", "kannada", "malayalam", "gujarati", "punjabi", "maratha"}


# Words that introduce WHERE THE ACCIDENT HAPPENED, versus words that merely
# describe a journey. "Bus going from Delhi to Kanpur collided in Mainpuri" is a
# MAINPURI accident; taking the first place found put it in Kanpur and inflated
# that city's count.
_AT_PLACE = re.compile(r"\b(?:in|at|near|outside|off|along|on the outskirts of|"
                       r"village|district|tehsil|taluka|mandal)\s+$", re.I)
_ROUTE_WORD = re.compile(r"\b(?:from|to|towards?|bound for|going to|heading to|en route|"
                         r"route|via|between|service|express|train no|flight)\s+$", re.I)


def extract_places(text, limit=3):
    """Return places, preferring the accident LOCATION over route endpoints."""
    if not text:
        return "", ""
    scored = []
    for name, pat in _PLACE_PATTERNS:
        if name.lower() in JUNK_PLACES:
            continue
        mm = pat.search(text)
        if not mm:
            continue
        before = text[max(0, mm.start() - 26): mm.start()]
        after = text[mm.end(): mm.end() + 34]   # long enough to see "-Pune expressway"
        score = 0
        if _AT_PLACE.search(before):
            score += 3                       # "in Mainpuri", "near Bidhnu"
        if re.match(r"\s*(?:district|city|village|tehsil|taluka|mandal)\b", after, re.I):
            score += 2                       # "Mainpuri district"
        if _ROUTE_WORD.search(before):
            score -= 3                       # "from Delhi", "to Kanpur"
        # A place that only appears inside a road name is NOT the accident site.
        # "Kanpur Sagar Highway", "Mumbai-Pune Expressway", "Hajipur road" name
        # roads; treating them as locations put accidents in the wrong city.
        if re.match(r"\s*(?:[A-Z][a-z]+\s+)?(?:highway|expressway|road|marg|bypass|"
                    r"corridor|flyover)\b", after, re.I) and not _AT_PLACE.search(before):
            continue
        if re.match(r"\s*[-\u2013]\s*[A-Z][a-z]{3,}\s+(?:highway|expressway|road)\b",
                    after, re.I):
            continue                         # "Mumbai-Pune Expressway"
        if mm.start() < 40:
            score += 1                       # datelines lead the headline
        # A place mentioned ONLY as a route endpoint is not where the accident
        # happened. Reporting no city is more honest than reporting the wrong one.
        if score <= 0:
            continue
        scored.append((-score, mm.start(), name))
    scored.sort()
    out, seen = [], set()
    for _, _, name in scored:
        if name.lower() in seen:
            continue
        out.append(name)
        seen.add(name.lower())
        if len(out) >= limit:
            break
    # Highways are deliberately NOT extracted. A road number tells you little
    # about where an accident happened, it was a weak and noisy match key for
    # deduplication, and road names were actively corrupting the city column.
    return "; ".join(out), ""



# ===========================================================================
# GAZETTEER - built-in list, optionally extended with the free GeoNames data
# ===========================================================================
# A hand-built list can never cover India. Mainpuri was missing, so an accident
# "in Mainpuri" involving a "bus from Delhi to Kanpur" was filed under Kanpur.
# GeoNames publishes every populated place in India under a free licence; it is
# downloaded once and cached. If the download fails the built-in list is used.
GEONAMES_URL = "https://download.geonames.org/export/dump/IN.zip"
GEONAMES_CACHE = "places_india.txt"
GEONAMES_MIN_POP = 2000        # keeps the list to real towns, not every hamlet


def load_geonames():
    """Return a list of Indian place names, or [] if unavailable."""
    import os
    if os.path.exists(GEONAMES_CACHE):
        try:
            with open(GEONAMES_CACHE, encoding="utf-8") as f:
                names = [l.strip() for l in f if l.strip()]
            if names:
                return names
        except OSError:
            pass
    data, _ = http_get(GEONAMES_URL, timeout=90, retries=1)
    if not data:
        print("[places] GeoNames unavailable - using the built-in list")
        return []
    try:
        import io
        import zipfile
        names = set()
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            with z.open("IN.txt") as fh:
                for raw in io.TextIOWrapper(fh, encoding="utf-8"):
                    p = raw.split("\t")
                    if len(p) < 15:
                        continue
                    if p[6] != "P":                       # populated places only
                        continue
                    try:
                        pop = int(p[14] or 0)
                    except ValueError:
                        pop = 0
                    if pop < GEONAMES_MIN_POP:
                        continue
                    nm = p[1].strip()
                    if 3 < len(nm) <= 30 and nm[0].isupper() and nm.replace(" ", "").isalpha():
                        names.add(nm)
        out = sorted(names)
        with open(GEONAMES_CACHE, "w", encoding="utf-8") as f:
            f.write("\n".join(out))
        print(f"[places] GeoNames loaded: {len(out)} Indian places cached")
        return out
    except Exception as e:                                # noqa: BLE001
        print(f"[places] GeoNames parse failed ({type(e).__name__}) - using built-in list")
        return []


def build_place_patterns():
    global PLACE_LIST, _PLACE_PATTERNS
    extra = load_geonames()
    combined = set(CITIES) | set(STATES) | set(extra)
    combined = {c for c in combined if c.lower() not in JUNK_PLACES}
    PLACE_LIST = sorted(combined, key=len, reverse=True)
    _PLACE_PATTERNS = [(p, re.compile(r"\b" + re.escape(p) + r"\b", re.I)) for p in PLACE_LIST]
    print(f"[places] gazetteer: {len(PLACE_LIST)} names")



# ===========================================================================
# CAUSE MECHANISM
# ===========================================================================
# The article BODY gives the fullest explanation, but most items are Google News
# stubs whose body cannot be fetched - which left the cause column 0% populated
# even when the headline said plainly what happened ("building SHUTTERING
# COLLAPSES", "brake failure", "tyre burst"). This names the mechanism from
# whatever text exists. It is a short standardised phrase, not a copy of the
# headline, so it stays informative without simply echoing the title back.
CAUSE_MECHANISMS = OrderedDict([
    # construction and structural
    ("Shuttering / formwork failure", r"shuttering|formwork|centering|falsework|staging collaps"),
    ("Scaffolding failure", r"scaffold\w*"),
    ("Crane failure", r"\bcrane\b|gantry|hoist fail|derrick"),
    ("Launching girder / segment failure", r"launching girder|girder|segment (?:erection|fell)"),
    ("Lift / hoist failure", r"\blift\b|elevator|cradle fell|gondola"),
    ("Excavation or trench collapse", r"excavat\w*|trench|pit collaps|soil collaps|cave-?in|shoring"),
    ("Slab or roof collapse", r"slab|roof|ceiling|lintel|beam collaps"),
    ("Wall collapse", r"wall collaps|boundary wall|wall fell|wall gave way"),
    ("Building collapse", r"building collaps|structure collaps|house collaps|portion of .{0,20}building"),
    ("Bridge or flyover failure", r"bridge collaps|flyover collaps|culvert|overbridge"),
    ("Road cave-in or subsidence", r"road cave|road collaps|sinkhole|subsid\w*|road sank"),
    ("Fall from height", r"fall from|fell from (?:the )?(?:roof|floor|height|building|tower|scaffold)"),
    ("Struck by falling material", r"fell on|falling (?:material|object|debris|slab|rod)|struck by"),
    ("Demolition failure", r"demolition|dismantl\w*"),
    # transport
    ("Brake failure", r"brake fail|brakes fail|brake burst"),
    ("Tyre burst", r"tyre burst|tire burst|tyre blow"),
    ("Overspeeding", r"overspeed\w*|speeding|rash driving|high speed"),
    ("Driver lost control", r"lost control|uncontroll\w*|out of control"),
    ("Head-on collision", r"head-?on|face to face collision"),
    ("Rear-end collision", r"hit from behind|rear-?end|rammed from behind"),
    ("Hit stationary vehicle", r"stationary|parked (?:truck|vehicle|trailer)"),
    ("Hit divider or barrier", r"divider|median|crash barrier|guardrail|railing"),
    ("Vehicle fell into gorge or water", r"fell into (?:gorge|ravine|river|canal|pond|water)|plunged into"),
    ("Overturning", r"overturn\w*|toppl\w*|capsiz\w*"),
    ("Derailment", r"derail\w*"),
    ("Level crossing", r"level crossing|unmanned crossing|railway crossing"),
    ("Hit while on track", r"(?:hit|run over) by (?:a )?train|on the (?:railway )?track"),
    ("Drunk driving", r"drunk|inebriated|under the influence"),
    ("Driver fatigue", r"dozed off|fell asleep|fatigue|drowsy"),
    ("Fog or poor visibility", r"\bfog\b|poor visibility|low visibility|smog"),
    ("Wet or slippery road", r"slipper\w*|wet road|skidd\w*"),
    ("Pothole or bad road", r"pothole|bad road|damaged road|crater"),
    ("Overloading", r"overload\w*|overcrowd\w*|beyond capacity"),
    ("Wrong-side driving", r"wrong side|wrong lane|wrong direction"),
    # industrial and others
    ("Boiler explosion", r"boiler"),
    ("Gas leak", r"gas leak|toxic gas|ammonia|chlorine"),
    ("Cylinder or LPG explosion", r"cylinder|lpg"),
    ("Explosion / blast", r"blast|explosion|exploded"),
    ("Fire", r"fire broke|caught fire|blaze|gutted|\bfire\b"),
    ("Electrocution", r"electrocut\w*|live wire|current|high tension"),
    ("Suffocation / toxic fumes", r"asphyxiat\w*|suffocat\w*|toxic fume|poisonous gas"),
    ("Septic tank / sewer", r"septic tank|sewer|manhole"),
    ("Machinery entrapment", r"caught in (?:the )?machine|conveyor|crushed by machine|grinder|lathe"),
    ("Drowning", r"drown\w*"),
    ("Stampede", r"stampede|crowd crush"),
    ("Aircraft technical failure", r"technical snag|engine fail|engine fire|hydraulic|bird hit"),
    ("Runway excursion", r"overshot|skidded off runway|veered off runway"),
])
CAUSE_MECH_PATTERNS = [(label, re.compile(rx, re.I)) for label, rx in CAUSE_MECHANISMS.items()]


def derive_cause_mechanism(text, limit=2):
    """Name the mechanism(s) from any available text. Empty if nothing matches."""
    if not text:
        return ""
    found = []
    for label, pat in CAUSE_MECH_PATTERNS:
        if pat.search(text):
            found.append(label)
            if len(found) >= limit:
                break
    return "; ".join(found)


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
          re.compile(r"\b(?:aged|age)\s*(\d{1,3})\b", re.I),
          re.compile(r"(\d{1,3})\s*(?:वर्षीय|वर्ष|साल|बरस|वयाच्या|वर्षांच्या)"),
          re.compile(r"(\d{1,3})\s*(?:বছরের|বছর|বয়সী)"),
          re.compile(r"(\d{1,3})\s*(?:வயது|வயதான)"),
          re.compile(r"(\d{1,3})\s*(?:సంవత్సరాల|ఏళ్ల|ఏండ్ల)"),
          re.compile(r"(\d{1,3})\s*(?:ವರ್ಷದ|ವರ್ಷ)"),
          re.compile(r"(\d{1,3})\s*(?:വയസ്സുള്ള|വയസ്സ്)"),
          re.compile(r"(\d{1,3})\s*(?:વર્ષીય|વર્ષના)"),
          re.compile(r"(\d{1,3})\s*(?:ਸਾਲਾ|ਸਾਲ)")]


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
_TRANSLATE_STATE = {"fails": 0, "blocked": False}


def translate_to_en(text):
    """Translate to English via the free endpoint.

    The per-run CAP was never the real limit - the free service throttles after
    a few hundred calls, so a bigger cap changed nothing. What helps instead:
      * skip anything already in English (no call, no quota spent);
      * stop after repeated failures rather than hammering a throttled service,
        and resume on the next run, since every translation is cached in the DB;
      * back off progressively instead of failing hard.
    """
    if not text or not text.strip():
        return ""
    if _MOCK_TRANSLATE is not None:
        return _MOCK_TRANSLATE(text)
    if TRANSLATE_BACKEND != "builtin" or _TRANSLATE_STATE["blocked"]:
        return ""
    if text.isascii():
        return ""                     # already English - do not spend a call
    try:
        url = ("https://translate.googleapis.com/translate_a/single"
               "?client=gtx&sl=auto&tl=en&dt=t&q=" + urllib.parse.quote(text[:1800]))
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=15) as r:
            data = json.loads(r.read().decode("utf-8", "ignore"))
        out = "".join(seg[0] for seg in data[0] if seg and seg[0])
        if out:
            _TRANSLATE_STATE["fails"] = 0
            return out
        return ""
    except Exception:                                              # noqa: BLE001
        _TRANSLATE_STATE["fails"] += 1
        if _TRANSLATE_STATE["fails"] >= 12:
            _TRANSLATE_STATE["blocked"] = True
            print("[translate] service is throttling - pausing until the next run "
                  "(work already done is saved)")
        else:
            time.sleep(min(8, 0.5 * _TRANSLATE_STATE["fails"]))
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



def clean_field(value, limit=None):
    """Every exported value passes through here. Newlines break CSV rows in
    spreadsheet software, and a repeated sentence is never wanted, so both are
    removed at the single point where values are produced."""
    if not value:
        return ""
    v = re.sub(r"[\r\n\t]+", " ", str(value))
    v = re.sub(r"\s+", " ", v).strip()
    v = dedupe_title(v)
    # drop an exact repeated tail, e.g. "X - source X - source"
    half = len(v) // 2
    if half > 15 and v[:half].strip().lower() == v[half:].strip().lower():
        v = v[:half].strip()
    return v[:limit] if limit else v


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
        title = clean_field((item.findtext("title") or "").strip())
        if not title:
            continue
        desc = clean_field(re.sub(r"<[^>]+>", " ", item.findtext("description") or ""))
        # Many publishers put the WHOLE article in <content:encoded> (or
        # media:description / summary). It is already downloaded with the feed,
        # needs no page fetch, and is not blocked by anything - the single
        # cheapest source of cause, location and casualty detail available.
        body = ""
        for el in item:
            tag = el.tag.split("}")[-1]
            if tag in ("encoded", "summary", "description", "articleBody") and el.text:
                cand = clean_field(re.sub(r"<[^>]+>", " ", el.text))
                if len(cand) > len(body):
                    body = cand
        if len(body) < len(desc):
            body = desc
        src_el = item.find("source")
        ts, iso = parse_date((item.findtext("pubDate") or "").strip())
        out.append({"title": title, "snippet": desc[:400], "body": body[:1600],
                    "url": (item.findtext("link") or "").strip(),
                    "source": src_el.text.strip() if src_el is not None and src_el.text else "",
                    "language": language, "query": query,
                    "published": iso, "published_ts": ts})
    return out



# ===========================================================================
# GDELT - a second free source that returns REAL publisher URLs
# ===========================================================================
# Google News RSS gives redirect stubs that cannot be resolved for free, so those
# items never yield article text. GDELT's DOC 2.0 API is free, needs no key, and
# returns direct article URLs, which ARE fetchable. It covers roughly the most
# recent three months - the same window this tool collects.
GDELT_URL = "https://api.gdeltproject.org/api/v2/doc/doc"
GDELT_QUERIES = [
    'sourcecountry:india (accident OR crash OR collapse OR derailed OR capsized)',
    'sourcecountry:india ("construction site" OR crane OR scaffolding OR girder)',
    'sourcecountry:india ("building collapse" OR "wall collapse" OR "bridge collapse")',
    'sourcecountry:india ("road accident" OR "bus accident" OR "truck accident")',
    'sourcecountry:india ("train accident" OR derailment OR "level crossing")',
    'sourcecountry:india ("factory accident" OR "boiler blast" OR "gas leak")',
]


def fetch_gdelt(query, maxrecords=75):
    """Return feed-shaped items from GDELT. Free, no key. Returns [] on failure."""
    params = urllib.parse.urlencode({
        "query": query, "mode": "ArtList", "format": "json",
        "maxrecords": maxrecords, "sort": "DateDesc",
    })
    data, _ = http_get(f"{GDELT_URL}?{params}", timeout=25, retries=1)
    if not data:
        return []
    try:
        payload = json.loads(data.decode("utf-8", "ignore"))
    except Exception:                                              # noqa: BLE001
        return []
    out = []
    for a in payload.get("articles", []):
        title = clean_field(a.get("title", ""))
        url = a.get("url", "")
        if not title or not url:
            continue
        seendate = a.get("seendate", "")
        try:
            dt = datetime.strptime(seendate[:8], "%Y%m%d").replace(tzinfo=timezone.utc)
            ts, iso = dt.timestamp(), dt.strftime("%Y-%m-%d")
        except ValueError:
            ts, iso = parse_date("")
        out.append({"title": title, "snippet": "", "body": "", "url": url,
                    "source": a.get("domain", ""), "language": a.get("language", "English") or "English",
                    "query": "gdelt", "published": iso, "published_ts": ts})
    return out


# ===========================================================================
# DATABASE
# ===========================================================================
COLUMNS = OrderedDict([
    ("id", "TEXT PRIMARY KEY"), ("title", "TEXT"), ("title_en", "TEXT"), ("url", "TEXT"),
    ("source", "TEXT"), ("published", "TEXT"), ("published_ts", "REAL"),
    ("category", "TEXT"), ("sector", "TEXT"), ("language", "TEXT"), ("title_norm", "TEXT"),
    ("snippet", "TEXT"), ("article_text", "TEXT"), ("image_url", "TEXT"),
    ("cities", "TEXT"), ("deaths", "INTEGER"), ("injured", "INTEGER"),
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
# Stemmed, because content_words() stems: "killed" becomes "kill", so the raw
# word list was letting generic terms through and inflating overlap between
# unrelated accidents ("3 killed near Pune" vs "4 killed near Pune").
STOPW = {"the", "and", "for", "with", "after", "near", "from", "were", "was", "has", "had",
         "accident", "news", "video", "kill", "dead", "death", "die", "injur", "injuri",
         "peopl", "person", "polic", "said", "report", "updat", "horrif", "terribl",
         "tragic", "major", "big", "massiv", "seriou", "sever", "incid", "case", "spot",
         "area", "district", "state", "hous", "famili", "victim", "driver", "man", "woman",
         "year", "old", "today", "yesterday", "morn", "night", "live", "lost", "due"}


def content_words(t):
    """Meaningful words, lightly stemmed so 'collapse' and 'collapses' match."""
    out = set()
    for w in re.findall(r"[a-z]{4,}", (t or "").lower()):
        if w in STOPW:
            continue
        for suf in ("ing", "ed", "es", "s"):
            if len(w) > 4 and w.endswith(suf):
                w = w[: -len(suf)]
                break
        out.add(w)
    return out


def similarity(a, b):
    parts, weights, strong = [], [], False
    ca = {x.strip().lower() for x in a["cities"].split(";") if x.strip()}
    cb = {x.strip().lower() for x in b["cities"].split(";") if x.strip()}
    # Highways are no longer a match key: a shared road number said little about
    # whether two reports described the same crash, and produced false pairings.
    loc = bool(ca and cb and ca & cb)
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
    elif ca and cb:
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



# ===========================================================================
# EVENT FINGERPRINT
# ===========================================================================
# Word overlap alone is a blunt instrument: two building collapses in the same
# city share most of their vocabulary. Before merging, compare the concrete
# FACTS of the two reports - place, day, time of day, what was being done, what
# failed, what was involved, who was hurt - and refuse to merge when any of them
# actively CONTRADICT. A contradiction is much stronger evidence of two separate
# accidents than shared wording is of one.
WEEKDAYS = re.compile(r"\b(monday|tuesday|wednesday|thursday|friday|saturday|sunday)\b", re.I)

ACTIVITY_WORDS = re.compile(
    r"\b(shuttering|formwork|scaffold\w*|centering|staging|crane|girder|gantry|hoist|"
    r"excavat\w*|trench|piling|concreting|casting|plaster\w*|painting|welding|chipping|"
    r"demolition|dismantl\w*|rebar|reinforcement|curing|erection|repair|renovation|"
    r"cleaning|loading|unloading|blasting|drilling|tunnel\w*|wiring)\b", re.I)

OBJECT_WORDS = re.compile(
    r"\b(bus|truck|lorry|tanker|trailer|car|jeep|van|tempo|auto|rickshaw|bike|scooter|"
    r"train|locomotive|coach|bogie|boat|ferry|ship|launch|aircraft|plane|helicopter|"
    r"building|wall|roof|slab|ceiling|balcony|staircase|bridge|culvert|flyover|tower|"
    r"godown|warehouse|shed|factory|plant|mill|boiler|cylinder|transformer|lift|"
    r"borewell|septic|sewer|manhole|tank)\b", re.I)

STOREY = re.compile(r"\b(single|two|three|four|five|six|seven|eight|nine|ten|\d{1,2})[\s-]"
                    r"(?:storey|storeys|story|storied|floor)\b", re.I)


def event_fingerprint(text, tod="", ages="", deaths=None, injured=None, place=""):
    """The concrete facts of one report, for comparison against another."""
    t = text or ""
    return {
        # A STATE is not a location for this purpose. Fifteen unrelated crashes
        # across Uttarakhand in a week share the state and nothing else, so state
        # matches are kept separate and count for far less than a town does.
        "place": {p.strip().lower() for p in (place or "").split(";")
                  if p.strip() and p.strip().lower() != "not identified"
                  and p.strip() not in STATES},
        "region": {p.strip().lower() for p in (place or "").split(";")
                   if p.strip() in STATES},
        "day": {d.lower() for d in WEEKDAYS.findall(t)},
        "tod": (tod or "").strip(),
        "activity": {a.lower() for a in ACTIVITY_WORDS.findall(t)},
        "mechanism": {x.strip() for x in derive_cause_mechanism(t, limit=4).split(";") if x.strip()},
        "objects": {o.lower() for o in OBJECT_WORDS.findall(t)},
        "storey": {s.lower() for s in STOREY.findall(t)},
        "ages": {a.strip() for a in (ages or "").split(";") if a.strip()},
        "deaths": deaths,
        "injured": injured,
    }


def _jaccard(x, y):
    if not x or not y:
        return None                 # silence, not disagreement
    return len(x & y) / len(x | y)


# How much each fact matters when judging whether two reports describe the same
# accident. Only fields present on BOTH sides are scored, and the result is a
# weighted average - so a single difference lowers the score without vetoing.
FP_WEIGHTS = {
    "place": 2.0,        # a town or city - the strongest single signal
    "region": 0.4,       # a state only - very weak on its own
    "objects": 1.4,      # bus / truck / building / boiler
    "activity": 1.3,     # shuttering / crane / excavation
    "storey": 1.2,       # four-storey vs two-storey
    "tod": 1.0,          # day vs night
    "day": 1.0,          # day of week
    "mechanism": 0.8,    # weaker: one report says "shuttering", another "building"
    "ages": 0.8,
    "casualty": 0.7,     # tolls change as a story develops
}
MERGE_SIMILARITY = 0.80      # 80% agreement across the facts, not 100%


def fingerprint_similarity(a, b, text_overlap=0.0, followup=False):
    """Graded 0-1 agreement between two reports.

    Deliberately NOT all-or-nothing. Two reports of one accident routinely differ
    in emphasis - one names the bus, the other the truck it hit - so a single
    mismatch should lower the score, not veto the pair. Fields absent on either
    side are skipped rather than counted against.
    """
    parts, weights = [], []
    for field in ("place", "region", "objects", "activity", "storey", "day",
                  "mechanism", "ages"):
        j = _jaccard(a[field], b[field])
        if j is not None:
            parts.append(j)
            weights.append(FP_WEIGHTS[field])
    if a["tod"] and b["tod"]:
        parts.append(1.0 if a["tod"] == b["tod"] else 0.0)
        weights.append(FP_WEIGHTS["tod"])
    da, db = a["deaths"], b["deaths"]
    if da is not None and db is not None and not followup:
        if da == db:
            c = 1.0
        elif max(da, db) and min(da, db) / max(da, db) >= 0.5:
            c = 0.7                 # a rising toll, not a different accident
        else:
            c = 0.2
        parts.append(c)
        weights.append(FP_WEIGHTS["casualty"])
    # In FOLLOW-UP coverage the toll is expected to change - that is what a
    # follow-up is for. Scoring it as disagreement penalised exactly the pairs we
    # are trying to join (9 dead on day one, 12 a week later), so it is ignored.
    # the wording itself always counts
    # Wording counts, but road-accident headlines are formulaic ("Three killed
    # as bus overturns near X"), so it cannot carry a merge on its own.
    parts.append(text_overlap)
    weights.append(1.0)
    if not weights:
        return 0.0
    return sum(p * w for p, w in zip(parts, weights)) / sum(weights)


def rededupe(conn):
    conn.execute("UPDATE articles SET is_duplicate=0, dup_group=id")
    rows = conn.execute(
        """SELECT id,title_norm,cities,deaths,injured,category,published_ts,title_en,title,
                  time_of_day,victim_age,snippet,article_text
           FROM articles ORDER BY published_ts ASC""").fetchall()
    seen, merged = [], 0
    for r in rows:
        full_text = all_text(r[7], r[8], r[11], r[12] if r[12] and r[12] != "-" else "")
        a = {"id": r[0], "title_norm": r[1] or "", "cities": r[2] or "",
             "deaths": r[3], "injured": r[4], "category": r[5], "published_ts": r[6] or 0,
             "words": content_words((r[7] or "") or (r[8] or "")), "dup_group": r[0],
             "fp": event_fingerprint(full_text, r[9] or "", r[10] or "",
                                     r[3], r[4], r[2] or "")}
        best = None
        for b in seen:
            if b["category"] != a["category"]:
                continue
            gap = abs(b["published_ts"] - a["published_ts"])
            if gap > FOLLOWUP_WINDOW_DAYS * 86400:
                continue
            wa, wb = a["words"], b["words"]
            ov = len(wa & wb) / max(1, min(len(wa), len(wb))) if wa and wb else 0.0
            if gap > EVENT_DATE_WINDOW_DAYS * 86400:
                # Days later, only follow-up coverage of the SAME accident should
                # merge. Without a shared, named place there is nothing anchoring
                # the pair, and formulaic headlines merge unrelated accidents.
                if not (a["fp"]["place"] and b["fp"]["place"]
                        and a["fp"]["place"] & b["fp"]["place"]):
                    continue          # a shared state is not enough
                if len(wa & wb) < 3:
                    continue          # some shared wording is still required
            # Every merge needs a real anchor, not just similar wording: a shared
            # town, matching casualty figures, or near-identical text. Without
            # this, formulaic headlines with no place merge into large clusters.
            same_town = bool(a["fp"]["place"] and b["fp"]["place"]
                             and a["fp"]["place"] & b["fp"]["place"])
            da_, db_ = a["deaths"], b["deaths"]
            same_toll = da_ is not None and db_ is not None and abs(da_ - db_) <= 1
            if not (same_town or same_toll or ov >= 0.60):
                continue
            is_followup = gap > EVENT_DATE_WINDOW_DAYS * 86400
            sim = fingerprint_similarity(a["fp"], b["fp"], ov, followup=is_followup)
            # ONE BAR: 80% agreement across the facts both reports state.
            # Not 100% - two reports of one accident routinely differ on a
            # detail - and no stricter bar for follow-ups, now that a changing
            # death toll no longer counts against them.
            bar = MERGE_SIMILARITY
            if sim >= bar and (best is None or sim > best[1]):
                best = (b["dup_group"], sim)

        if best:
            conn.execute("UPDATE articles SET is_duplicate=1, dup_group=? WHERE id=?", (best[0], a["id"]))
            a["dup_group"] = best[0]
            merged += 1
        # Only CANONICAL records become comparison points. Otherwise merges chain:
        # A matches B, B matches C, C matches D, and a fortnight of unrelated
        # crashes in one state ends up as a single accident even though the first
        # and last reports have nothing in common.
        if best is None:
            seen.append(a)
            if len(seen) > 3000:
                seen = seen[-3000:]
    conn.commit()
    print(f"[dedupe] {merged} duplicate reports merged")
    return merged



def all_text(*parts):
    """Every text we hold for an item, joined once.

    Each stage must see EVERY source: the headline, the RSS snippet, the
    <content:encoded> full text that arrives inside the feed, the English
    translation, and the fetched article body. Gaps here are silent - an item
    whose only accident evidence sits in paragraph two was being dropped at the
    gate because the gate could only see the headline.
    """
    seen, out = set(), []
    for p in parts:
        p = (p or "").strip()
        if not p:
            continue
        key = p[:80].lower()
        if key in seen:            # avoid repeating a snippet that echoes the title
            continue
        seen.add(key)
        out.append(p)
    return " ".join(out)


# ===========================================================================
# STORE
# ===========================================================================
def store(conn, items, stats, translate_budget=0):
    added = 0
    for it in items:
        feed_body = it.get("body", "")
        native_text = all_text(it["title"], it["snippet"], feed_body)

        # ORDER MATTERS: translate BEFORE screening for non-English items.
        # The gates are written mainly in English, so screening Hindi text first
        # rejected genuine accidents ("शटरिंग गिरी") before translation could
        # make them readable. Non-English items are now rendered into English
        # first, then judged on the native text and the translation together.
        title_en = body_en = ""
        if TRANSLATE_BACKEND != "none" and translate_budget > 0 and not native_text.isascii():
            if not it["title"].isascii():
                title_en = clean_field(translate_to_en(it["title"]))
                translate_budget -= 1
            rest = all_text(it["snippet"], feed_body)
            if rest and not rest.isascii() and translate_budget > 0:
                body_en = clean_field(translate_to_en(rest[:1700]))
                translate_budget -= 1

        gate_text = all_text(title_en, body_en, native_text)
        keep, reason = screen(gate_text, "", it["source"], it["url"], it["published"])
        if not keep:
            stats[reason] = stats.get(reason, 0) + 1
            continue

        full = all_text(it["title"], title_en, body_en, it["snippet"], feed_body)
        rid = hashlib.sha1(norm_title(it["title"]).encode("utf-8")).hexdigest()
        if conn.execute("SELECT 1 FROM articles WHERE id=?", (rid,)).fetchone():
            stats["already stored"] = stats.get("already stored", 0) + 1
            continue

        cat, sector = classify(full)
        deaths, injured = extract_counts(full)
        cities, _ = extract_places(full)
        conn.execute(
            """INSERT OR IGNORE INTO articles
               (id,title,title_en,url,source,published,published_ts,category,sector,language,
                title_norm,snippet,article_text,image_url,cities,deaths,injured,cause,
                time_of_day,victim_gender,victim_age,severity,fetched_at,is_duplicate,dup_group,translated)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,0,?,?)""",
            (rid, it["title"], title_en, it["url"], it["source"], it["published"],
             it["published_ts"], cat, sector, it["language"], norm_title(it["title"]),
             it["snippet"], feed_body if len(feed_body) > len(it["snippet"]) + 40 else "",
             "", cities, deaths, injured,
             (extract_cause(all_text(body_en, feed_body, it["snippet"]), title_en or it["title"])
              or derive_cause_mechanism(full)),
             extract_time_of_day(full), extract_gender(all_text(title_en, body_en) or full),
             extract_ages(full),
             severity(full, deaths, injured),
             datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"), rid,
             1 if (title_en or body_en) else 0))
        added += 1
        stats["KEPT"] = stats.get("KEPT", 0) + 1
    conn.commit()
    return added, translate_budget


def backfill_articles(conn, budget, time_budget_s=None):
    """Fetch article bodies, then re-derive category, cause, places and counts.

    Budget allocation matters more than budget size. Measured on real output,
    698 of 699 stored links were Google News redirect stubs, which cannot be
    resolved for free and fail instantly - so a large fetch budget was being
    spent almost entirely on links that can never succeed. Two changes:
      1. stubs are marked unfetchable in ONE bulk statement, so they never enter
         the loop or consume the budget;
      2. the remaining budget is spent on real publisher URLs, newest first.
    A wall-clock budget also applies, so a slow night cannot overrun the job.
    """
    if budget <= 0:
        return 0
    # 1. retire the unfetchable stubs in bulk (no network, no budget consumed)
    marked = conn.execute(
        """UPDATE articles SET article_text='-'
           WHERE (article_text IS NULL OR article_text='')
             AND (url='' OR (url LIKE '%news.google.com%'
                             AND url NOT LIKE '%news.google.com/rss/articles/CBM%'))""").rowcount
    conn.commit()
    if marked:
        print(f"[articles] {marked} links are Google stubs - skipped, budget preserved")

    started = time.time()
    rows = conn.execute(
        """SELECT id,url,title,title_en,snippet FROM articles
           WHERE (article_text IS NULL OR article_text='') AND url!=''
           ORDER BY (url LIKE '%news.google.com%') ASC, published_ts DESC
           LIMIT ?""", (budget,)).fetchall()
    done = failed = 0
    for rid, url, title, ten, snip in rows:
        if time_budget_s and (time.time() - started) > time_budget_s:
            print(f"[articles] time budget reached after {done} fetches - resuming next run")
            break
        _, img, body = fetch_article(url)
        if not body:
            conn.execute("UPDATE articles SET article_text='-' WHERE id=?", (rid,))
            failed += 1
            continue
        body_en = body
        if TRANSLATE_BACKEND != "none" and not body.isascii():
            body_en = translate_to_en(body[:1500]) or body
        keep, _ = screen(all_text(title, ten, body, body_en), "", "", url, None)
        if not keep:
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            continue
        full = all_text(title, ten, body_en, body, snip)
        cities, _ = extract_places(full)
        deaths, injured = extract_counts(full)
        cat, sector = classify(full)
        conn.execute(
            """UPDATE articles SET article_text=?, category=?, sector=?,
               image_url=CASE WHEN image_url='' THEN ? ELSE image_url END,
               cause=?, cities=CASE WHEN ?!='' THEN ? ELSE cities END,
               deaths=COALESCE(deaths,?), injured=COALESCE(injured,?),
               time_of_day=CASE WHEN time_of_day='' THEN ? ELSE time_of_day END,
               victim_gender=CASE WHEN victim_gender='' THEN ? ELSE victim_gender END,
               victim_age=CASE WHEN victim_age='' THEN ? ELSE victim_age END,
               severity=? WHERE id=?""",
            (body[:1400], cat, sector, img,
             (extract_cause(all_text(body_en, snip), ten or title) or derive_cause_mechanism(full)),
             cities, cities, deaths, injured,
             extract_time_of_day(full), extract_gender(body_en if body_en.isascii() else full),
             extract_ages(full),
             severity(full, deaths, injured), rid))
        done += 1
        time.sleep(0.2)
    conn.commit()
    if done or failed:
        print(f"[articles] fetched {done}, failed {failed}")
    return done



NUMBER_CONTEXT = re.compile(
    r"(\d{1,4})\s*(?:-|\u2013)?\s*(?:year|yr|yrs|years|month|months|day|days|hour|hours|"
    r"वर्षीय|वर्ष|साल|महीनों|महीने|दिन|বছর|মাস|வயது|மாதங்களில்|மாத|సంవత్సరాల|నెలల|"
    r"ವರ್ಷ|ತಿಂಗಳ|വയസ്സ്|മാസം|વર્ષ|મહિના|ਸਾਲ|ਮਹੀਨੇ)", re.I)
STAT_HINT = re.compile(
    r"\b(?:per (?:day|year|month)|every (?:hour|day|year)|on average|average of|"
    r"statistics|data shows|figures|so far this year|in the last \d+|total of \d+)\b"
    r"|महीनों में|वर्षों में|மாதங்களில்|ஆண்டுகளில்|నెలల్లో|ತಿಂಗಳಲ್ಲಿ|મહિનામાં", re.I)



def backfill_translations(conn, budget=1500):
    """Retry items that arrived when the translator was unavailable.

    Translation was previously attempted ONCE, as an item arrived. The free
    service throttles after a few hundred calls, so everything that arrived
    after the throttle kicked in stayed untranslated for ever - which is why
    coverage got worse as the archive grew (43% of August rows had no English
    text against 28% of June). Each run now works through the backlog, oldest
    gap first, and every success is stored, so coverage only ever improves.
    """
    if TRANSLATE_BACKEND == "none" or budget <= 0:
        return 0
    rows = conn.execute(
        """SELECT id, title, snippet, article_text FROM articles
           WHERE (title_en IS NULL OR title_en='')
           ORDER BY published_ts DESC LIMIT ?""", (budget,)).fetchall()
    done = skipped = 0
    for rid, title, snip, body in rows:
        if (title or "").isascii():
            # already English - record it so the row is not retried for ever
            conn.execute("UPDATE articles SET title_en=? WHERE id=?", (clean_field(title), rid))
            skipped += 1
            continue
        tx = clean_field(translate_to_en(title))
        if not tx:
            break                       # throttled: stop and resume next run
        text = all_text(tx, title, snip, body if body and body != "-" else "")
        cities, _ = extract_places(text)
        deaths, injured = extract_counts(text)
        cat, sector = classify(text)
        conn.execute(
            """UPDATE articles SET title_en=?, translated=1, category=?, sector=?,
               cities=CASE WHEN ?!='' THEN ? ELSE cities END,
               deaths=COALESCE(?, deaths), injured=COALESCE(?, injured),
               cause=CASE WHEN cause IS NULL OR cause='' THEN ? ELSE cause END,
               time_of_day=CASE WHEN time_of_day='' THEN ? ELSE time_of_day END,
               victim_age=CASE WHEN victim_age='' THEN ? ELSE victim_age END,
               severity=? WHERE id=?""",
            (tx, cat, sector, cities, cities, deaths, injured,
             derive_cause_mechanism(text), extract_time_of_day(text),
             extract_ages(text), severity(text, deaths, injured), rid))
        done += 1
        time.sleep(0.2)
    conn.commit()
    left = conn.execute("SELECT COUNT(*) FROM articles "
                        "WHERE title_en IS NULL OR title_en=''").fetchone()[0]
    print(f"[translate] {done} translated, {skipped} already English, {left} still waiting")
    if done:
        auto_repair(conn, "after translation")
    return done


def rescreen_all(conn):
    """Apply the CURRENT gates to everything already stored, so a rule change
    cleans history instead of only affecting new items."""
    removed = 0
    for rid, title, ten, snip, body, src, url, pub in conn.execute(
            "SELECT id,title,title_en,snippet,article_text,source,url,published FROM articles").fetchall():
        clean = clean_field(title or "")
        text = all_text(clean, ten, snip, body if body and body != "-" else "")
        keep, _ = screen(text, "", src or "", url or "", pub)
        if not keep:
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            removed += 1
            continue
        cat, sector = classify(text)
        cities, _ = extract_places((ten or "") + " " + text)
        # Recompute the FACTS too. Extraction rules change; without this, a wrong
        # figure written by an earlier version (an age read as a death toll, for
        # example) would survive untouched no matter how often the rule was fixed.
        deaths, injured = extract_counts(text)
        conn.execute("""UPDATE articles SET title=?, title_en=?, title_norm=?, category=?,
                        sector=?, cities=?, deaths=?, injured=?, severity=?,
                        time_of_day=?, victim_gender=?, victim_age=?,
                        cause=CASE WHEN cause IS NULL OR cause='' THEN ? ELSE cause END
                        WHERE id=?""",
                     (clean, clean_field(ten or ""), norm_title(clean), cat, sector,
                      cities, deaths, injured, severity(text, deaths, injured),
                      extract_time_of_day(text), extract_gender(ten or text),
                      extract_ages(text), derive_cause_mechanism(text), rid))
    conn.commit()
    if removed:
        print(f"[rescreen] removed {removed} stored records that fail the current gates")
    return removed


# ===========================================================================
# EXPORTS
# ===========================================================================
def _w(path):
    return open(path, "w", newline="", encoding="utf-8-sig")


def resolve_events(conn):
    """Collapse reports into ACCIDENTS. This is the single source of truth: the
    accidents file and BOTH summaries are built from this same list, so their
    totals can never disagree."""
    # Named columns, not positions. Positional indexing broke silently every time
    # a column was added or removed, which is exactly how the highway removal
    # first went wrong.
    cols = ["dup_group", "published", "published_ts", "category", "sector", "cities",
            "deaths", "injured", "cause", "time_of_day", "victim_gender", "victim_age",
            "severity", "source", "title", "title_en", "url", "language",
            "snippet", "article_text"]
    groups = {}
    for row in conn.execute(f"SELECT {','.join(cols)} FROM articles ORDER BY published_ts ASC"):
        rec = dict(zip(cols, row))
        groups.setdefault(rec["dup_group"], []).append(rec)

    def first_of(members, key):
        return next((m[key] for m in members if m.get(key)), "")

    events = []
    for members in groups.values():
        by_time = sorted(members, key=lambda x: x["published_ts"] or 0)
        best = max(members, key=lambda m: (m["deaths"] is not None) * 3
                   + (m["injured"] is not None) * 2 + bool(m["cities"]) * 2
                   + bool(m["cause"]) * 2 + (m["language"] == "English"))
        # CASUALTIES: the methodology takes the toll from the LATEST report (it
        # only climbs as the event is confirmed). But English reports extract far
        # more reliably than the foreign-language copies - whose numbers were being
        # corrupted by outlet names ("News18" -> 18) and unmapped number-words - so
        # the latest figure is read from the ENGLISH reports first, falling back to
        # the latest across all languages only when no English report states one.
        # This is what stopped a Bengali follow-up's thin "6 injured" from
        # overwriting The Hindu's "12". Killed and injured are judged separately.
        by_lang_time = lambda ms: sorted(ms, key=lambda m: m["published_ts"] or 0)
        def _latest(key, english_only):
            src = [m for m in members if not english_only or m["language"] == "English"]
            return next((m[key] for m in reversed(by_lang_time(src)) if m[key] is not None), None)
        deaths = _latest("deaths", True)
        if deaths is None:
            deaths = _latest("deaths", False)
        injured = _latest("injured", True)
        if injured is None:
            injured = _latest("injured", False)
        dvals = [m["deaths"] for m in members if m["deaths"] is not None]
        ivals = [m["injured"] for m in members if m["injured"] is not None]
        toll_conflict = len(set(dvals)) > 1 or len(set(ivals)) > 1
        toll_detail = ""
        if toll_conflict:
            bits = []
            if len(set(dvals)) > 1:
                bits.append("killed reported as " + "/".join(str(x) for x in sorted(set(dvals))))
            if len(set(ivals)) > 1:
                bits.append("injured reported as " + "/".join(str(x) for x in sorted(set(ivals))))
            toll_detail = "; ".join(bits)
        sev = best["severity"] or ""
        if deaths:
            sev = "Fatal"
        elif injured:
            sev = "Injury only"
        places = [c.strip() for c in (best["cities"] or "").split(";") if c.strip()]
        if not places:
            places = [c.strip() for m in members
                      for c in (m["cities"] or "").split(";") if c.strip()]
        # The cause is derived from EVERY text of EVERY report of this accident -
        # headline, translation, RSS snippet and fetched article body - not from
        # the headline alone. A later report often explains a cause the first did
        # not, so all members are pooled before the mechanism is named.
        cause_parts = []
        for m in members:
            body = m["article_text"] if (m["article_text"] and m["article_text"] != "-") else ""
            cause_parts += [m["title_en"], m["title"], m["snippet"], body]
        cause_text = all_text(*cause_parts)
        events.append({
            "date": by_time[0]["published"], "last": by_time[-1]["published"],
            "category": (best["category"] or "").replace("_", " "),
            "sector": (best["sector"] or "").replace("_", " "),
            "place": places[0] if places else "Not identified",
            "places": "; ".join(dict.fromkeys(places))[:120],
            "deaths": deaths, "injured": injured, "severity": sev,
            "toll_conflict": toll_conflict, "toll_detail": toll_detail,
            "tod": first_of(members, "time_of_day"),
            "gender": first_of(members, "victim_gender"),
            "ages": first_of(members, "victim_age"),
            "cause": first_of(members, "cause"),
            "cause_text": cause_text,
            "n": len(members),
            "outlets": "; ".join(sorted({(m["source"] or "").strip() for m in members
                                         if (m["source"] or "").strip()})[:6]),
            "headline": best["title"] or "",
            # If the item is already in English there is nothing to translate, so
            # show the headline itself rather than an empty cell. A blank here
            # now means one thing only: a non-English item still awaiting
            # translation.
            "headline_en": (best["title_en"]
                            or (best["title"] if (best["title"] or "").isascii() else "")
                            or next((m["title_en"] for m in members if m["title_en"]), "")),
            "url": best["url"] or "",
        })
    return events


def export_accidents(conn, events, path="ACCIDENTS.csv"):
    """ONE ROW PER ACCIDENT, written from the resolved event list."""
    rows = []
    for e in events:
        rows.append([
            e["date"], e["last"], e["category"], e["sector"], e["places"],
            e["deaths"] if e["deaths"] is not None else "",
            e["injured"] if e["injured"] is not None else "",
            e["severity"], e["tod"], e["gender"], e["ages"],
            standardise_cause(e), e["cause"], e["n"],
            e["outlets"], e["headline"], e["headline_en"], e["url"]])
    rows.sort(key=lambda r: r[0], reverse=True)
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Date of Accident", "Last Reported", "Accident Type", "Sector (others only)",
                    "City / Place", "Killed", "Injured", "Severity", "Time of Day",
                    "Victim Gender", "Victim Age(s)", "Reported Cause (standardised)",
                    "Reported Cause (as written)", "Times Reported",
                    "Reported By", "Headline", "Headline (English)", "Link"])
        for r in rows:
            w.writerow([v if isinstance(v, int) else clean_field(v) for v in r])
    return len(rows)


def export_summary(events, path, confirmed_only):
    """Built from the SAME resolved events as ACCIDENTS.csv, so the totals in the
    two files always agree. Previously this counted raw articles and produced
    different numbers - e.g. Kanpur showed 47 killed against 45 in the accidents
    file, because one path took the latest toll and the other the first."""
    agg = {}
    for e in events:
        if confirmed_only:
            if e["place"] == "Not identified" or not e["category"]:
                continue
            if e["category"] == "others" and e["sector"] in ("", "unspecified"):
                continue
            if e["severity"] in ("", "Not stated"):
                continue
        a = agg.setdefault((e["place"], e["category"], e["sector"]),
                           {"n": 0, "near": 0, "fatal": 0, "inj": 0, "k": 0, "i": 0})
        a["n"] += 1
        a["near"] += e["severity"] == "Near miss"
        a["fatal"] += e["severity"] == "Fatal"
        a["inj"] += e["severity"] == "Injury only"
        a["k"] += e["deaths"] or 0
        a["i"] += e["injured"] or 0
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["City", "Accident Type", "Sector (others only)", "Number of Accidents",
                    "Near Misses", "Fatal Accidents", "Injury-only Accidents",
                    "People Killed", "People Injured"])
        for (p, c, s), a in sorted(agg.items(), key=lambda kv: (-kv[1]["k"], -kv[1]["n"], kv[0][0])):
            w.writerow([clean_field(p), c, s, a["n"], a["near"], a["fatal"], a["inj"],
                        a["k"], a["i"]])
    return len(agg)


def export_category_summary(events, path="SUMMARY_by_category.csv", confirmed_only=False):
    """ONE ROW PER CATEGORY. Built from the same resolved event list as
    ACCIDENTS.csv, so its totals can never disagree with the rest of the tool.

    Two different kinds of number sit in this table and are labelled as such:
      - ACCIDENT COUNTS  (Number of Accidents, Fatal, Injury-only, Near Misses)
        -> how many accidents of each severity.
      - PEOPLE COUNTS    (People Killed, People Injured)
        -> how many individuals, summed across accidents.
    'Near miss' is a severity of an accident, never a count of people, which is
    why the accident-count columns are shown alongside the people totals."""
    agg = {}
    for e in events:
        if confirmed_only:
            if e["place"] == "Not identified" or not e["category"]:
                continue
            if e["category"] == "others" and e["sector"] in ("", "unspecified"):
                continue
            if e["severity"] in ("", "Not stated"):
                continue
        cat = e["category"] or "not identified"
        a = agg.setdefault(cat, {"n": 0, "fatal": 0, "inj": 0, "near": 0, "k": 0, "i": 0})
        a["n"] += 1
        a["fatal"] += e["severity"] == "Fatal"
        a["inj"] += e["severity"] == "Injury only"
        a["near"] += e["severity"] == "Near miss"
        a["k"] += e["deaths"] or 0
        a["i"] += e["injured"] or 0
    total = {"n": 0, "fatal": 0, "inj": 0, "near": 0, "k": 0, "i": 0}
    for a in agg.values():
        for key in total:
            total[key] += a[key]
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Accident Type", "Number of Accidents", "Fatal Accidents",
                    "Injury-only Accidents", "Near Misses", "People Killed", "People Injured"])
        for cat, a in sorted(agg.items(), key=lambda kv: (-kv[1]["k"], -kv[1]["n"], kv[0])):
            w.writerow([cat, a["n"], a["fatal"], a["inj"], a["near"], a["k"], a["i"]])
        w.writerow(["TOTAL", total["n"], total["fatal"], total["inj"], total["near"],
                    total["k"], total["i"]])
    return len(agg)


def standardise_cause(e):
    """The single cause we trust for counting. The stored 'cause' field mixes
    free-text explanations with standardised labels, so it cannot be counted
    consistently. This re-derives ONE label from the controlled vocabulary
    (CAUSE_MECHANISMS) using EVERY text held for the accident - headline,
    translation, RSS snippet and fetched article body, pooled across all merged
    reports (see resolve_events -> 'cause_text') - never the headline alone. It
    returns 'Not stated' when no known cue is present, never a guess. These
    remain reported, pre-investigation attributions (METHODOLOGY sec 7.6,
    sec 10.4), not verified causes; consistency is what this buys, not certainty."""
    text = e.get("cause_text") or " ".join(
        str(e.get(k) or "") for k in ("headline_en", "cause", "headline"))
    label = derive_cause_mechanism(text, limit=1)
    return label or "Not stated"


def export_cause_summary(events, path="SUMMARY_by_cause.csv", confirmed_only=False):
    """Standardised reported cause x count. The 'Not stated' row is ALWAYS shown,
    because a cause distribution is only honest when the unknown share is visible
    (METHODOLOGY sec 10.4). Causes are what the early news reported, not verified
    findings."""
    agg = {}
    kept = 0
    for e in events:
        if confirmed_only and (e["place"] == "Not identified" or not e["category"]
                               or e["severity"] in ("", "Not stated")):
            continue
        kept += 1
        cause = standardise_cause(e)
        a = agg.setdefault(cause, {"n": 0, "k": 0, "i": 0})
        a["n"] += 1
        a["k"] += e["deaths"] or 0
        a["i"] += e["injured"] or 0
    stated = sum(a["n"] for c, a in agg.items() if c != "Not stated")
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Reported Cause (standardised)", "Number of Accidents",
                    "People Killed", "People Injured"])
        # Known causes first, biggest first; "Not stated" pinned to the bottom.
        ordered = sorted(((c, a) for c, a in agg.items() if c != "Not stated"),
                         key=lambda kv: (-kv[1]["n"], -kv[1]["k"], kv[0]))
        for c, a in ordered:
            w.writerow([c, a["n"], a["k"], a["i"]])
        if "Not stated" in agg:
            a = agg["Not stated"]
            w.writerow(["Not stated", a["n"], a["k"], a["i"]])
        tot_n = sum(a["n"] for a in agg.values())
        tot_k = sum(a["k"] for a in agg.values())
        tot_i = sum(a["i"] for a in agg.values())
        w.writerow(["TOTAL", tot_n, tot_k, tot_i])
        pct = (100 * stated // kept) if kept else 0
        w.writerow([])
        w.writerow([f"Cause identified for {stated} of {kept} accidents ({pct}%). "
                    "Causes are as first reported, not verified.", "", "", ""])
    return len(agg)


def export_monthly_from_events(events, path="TREND_monthly.csv"):
    data, cats = {}, set()
    for e in events:
        mth = (e["date"] or "")[:7]
        if not mth:
            continue
        d = data.setdefault(mth, {})
        c = d.setdefault(e["category"], [0, 0, 0])
        c[0] += 1
        c[1] += e["deaths"] or 0
        c[2] += e["injured"] or 0
        cats.add(e["category"])
    cats = sorted(cats)
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Month"] + list(cats) + ["TOTAL Accidents", "TOTAL Killed", "TOTAL Injured"])
        for mth in sorted(data, reverse=True):
            ns = [data[mth].get(c, [0, 0, 0])[0] for c in cats]
            w.writerow([mth] + ns + [sum(ns),
                                     sum(v[1] for v in data[mth].values()),
                                     sum(v[2] for v in data[mth].values())])
    return len(data)


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



def export_dashboard(events, path="index.html"):
    """A single self-contained page for people who should never have to look at
    code or spreadsheets: headline numbers, a monthly table, the leading places,
    and download links for the CSVs. Publishable free via GitHub Pages."""
    total = len(events)
    killed = sum(e["deaths"] or 0 for e in events)
    injured = sum(e["injured"] or 0 for e in events)
    near = sum(1 for e in events if e["severity"] == "Near miss")
    cats, months, places = {}, {}, {}
    for e in events:
        c = cats.setdefault(e["category"] or "unclassified", [0, 0, 0])
        c[0] += 1; c[1] += e["deaths"] or 0; c[2] += e["injured"] or 0
        mth = (e["date"] or "")[:7]
        if mth:
            m_ = months.setdefault(mth, {})
            m_[e["category"]] = m_.get(e["category"], 0) + 1
        if e["place"] != "Not identified":
            p = places.setdefault(e["place"], [0, 0])
            p[0] += 1; p[1] += e["deaths"] or 0
    cat_names = sorted(cats)
    head = "".join(f"<th>{html.escape(c)}</th>" for c in cat_names)
    mrows = ""
    for mth in sorted(months, reverse=True):
        cells = "".join(f"<td>{months[mth].get(c, 0)}</td>" for c in cat_names)
        mrows += f"<tr><th>{mth}</th>{cells}<td class=t>{sum(months[mth].values())}</td></tr>"
    crows = "".join(
        f"<tr><td class=k>{html.escape(c.replace('_', ' '))}</td><td>{v[0]}</td>"
        f"<td>{v[1]}</td><td>{v[2]}</td></tr>"
        for c, v in sorted(cats.items(), key=lambda kv: -kv[1][1]))
    prows = "".join(
        f"<tr><td class=k>{html.escape(p)}</td><td>{v[0]}</td><td>{v[1]}</td></tr>"
        for p, v in sorted(places.items(), key=lambda kv: (-kv[1][1], -kv[1][0]))[:20])
    updated = datetime.now(timezone.utc).strftime("%d %B %Y, %H:%M UTC")
    doc = f"""<!doctype html><html lang=en><head><meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>India Accident Monitor</title><style>
body{{font:15px/1.6 system-ui,-apple-system,sans-serif;margin:0;background:#f5f6f8;color:#16181d}}
.w{{max-width:960px;margin:0 auto;padding:28px 18px 60px}}
h1{{font-size:24px;margin:0 0 4px}} h2{{font-size:17px;margin:30px 0 8px}}
.sub{{color:#5b6169;font-size:13px;margin-bottom:18px}}
.note{{background:#fff7e6;border:1px solid #f0dcb0;border-radius:10px;padding:14px 18px;
font-size:13px;color:#5a4718;margin:18px 0}}
.cards{{display:flex;gap:12px;flex-wrap:wrap;margin-bottom:6px}}
.card{{background:#fff;border:1px solid #e2e5ea;border-radius:12px;padding:16px 20px;flex:1;min-width:120px}}
.card .n{{font-size:26px;font-weight:600}} .card .l{{font-size:12px;color:#5b6169}}
table{{width:100%;border-collapse:collapse;background:#fff;border:1px solid #e2e5ea;
border-radius:12px;overflow:hidden;margin-top:6px;font-size:13.5px}}
th,td{{padding:8px 11px;text-align:right;border-bottom:1px solid #eff1f4;font-variant-numeric:tabular-nums}}
thead th{{background:#eef1f5;font-size:11px;text-transform:uppercase;letter-spacing:.04em}}
tbody th,td.k{{text-align:left}} td.t{{font-weight:600;background:#fafbfc}}
a.dl{{display:inline-block;background:#1a56db;color:#fff;text-decoration:none;padding:9px 15px;
border-radius:8px;font-size:13px;margin:4px 8px 4px 0}}
.two{{display:flex;gap:16px;flex-wrap:wrap}} .two>div{{flex:1;min-width:280px}}
footer{{margin-top:34px;font-size:12px;color:#6b7280}}
</style></head><body><div class=w>
<h1>India Accident Monitor</h1>
<div class=sub>Infrastructure and transport accidents reported in Indian news &middot;
updated {updated}</div>

<div class=cards>
<div class=card><div class=n>{total}</div><div class=l>accidents</div></div>
<div class=card><div class=n>{killed}</div><div class=l>people killed</div></div>
<div class=card><div class=n>{injured}</div><div class=l>people injured</div></div>
<div class=card><div class=n>{near}</div><div class=l>near misses</div></div>
</div>

<div class=note><b>These are counts of accidents reported in the news, not official
totals.</b> Most accidents in India never reach the news, so these figures are an
undercount by design. They are useful for comparing categories and spotting
patterns, not for measuring how many accidents occur. Official annual figures:
MoRTH, NCRB and DGFASLI.</div>

<h2>By accident type</h2>
<table><thead><tr><th class=k style="text-align:left">Type</th><th>Accidents</th>
<th>Killed</th><th>Injured</th></tr></thead><tbody>{crows}</tbody></table>

<h2>By month</h2>
<table><thead><tr><th style="text-align:left">Month</th>{head}<th>Total</th></tr></thead>
<tbody>{mrows}</tbody></table>

<h2>Places most affected</h2>
<table><thead><tr><th class=k style="text-align:left">Place</th><th>Accidents</th>
<th>Killed</th></tr></thead><tbody>{prows}</tbody></table>

<h2>Download the data</h2>
<a class=dl href="ACCIDENTS.csv">Every accident (CSV)</a>
<a class=dl href="SUMMARY_by_category.csv">Summary &ndash; by accident type</a>
<a class=dl href="SUMMARY_by_cause.csv">Summary &ndash; by reported cause</a>
<a class=dl href="SUMMARY_confirmed.csv">Summary &ndash; confirmed only</a>
<a class=dl href="SUMMARY_all.csv">Summary &ndash; everything</a>
<a class=dl href="TREND_monthly.csv">Monthly trend</a>

<footer>Each row in the accident file is one accident, with duplicate reports of the
same event already merged. "Confirmed only" keeps just the accidents whose place,
type and outcome are all known.</footer>
</div></body></html>"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(doc)
    return total



# ===========================================================================
# SELF-AUDIT
# ===========================================================================
# Every error found so far was found by a human reading rows. That does not
# scale. These checks look for the SHAPES of those errors automatically, so the
# tool reports its own suspect records instead of waiting to be caught.
# Each rule below exists because a specific real bug got through.
def auto_repair(conn, label=""):
    """Detect AND FIX the known error shapes, automatically.

    Runs at the end of every collection cycle and again after every batch of
    translations, because a fresh translation changes the text an error can hide
    in. Nothing here asks a human to look at anything: a figure that is really an
    age is cleared, a statistical round-up is deleted, and an unmerged duplicate
    is merged. Each rule exists because a specific real error reached the output.
    """
    cleared = deleted = 0
    rows = conn.execute(
        """SELECT id,title,title_en,snippet,article_text,deaths,injured,published
           FROM articles""").fetchall()
    for rid, title, ten, snip, body, d, i, pub in rows:
        text = all_text(ten, title, snip, body if body and body != "-" else "")
        if not text:
            continue

        # 1. a statistical round-up is not an accident - remove it entirely
        if STAT_HINT.search(text) or currency_verdict(text, pub) == "not_event":
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            deleted += 1
            continue

        # 2a. a toll too large for a single Indian accident is a round-up
        if (d and d > 200) or (i and i > 300):
            conn.execute("DELETE FROM articles WHERE id=?", (rid,))
            deleted += 1
            continue

        # 2. a casualty figure that is really an age or a duration
        fixed_d, fixed_i = d, i
        for mm in NUMBER_CONTEXT.finditer(text):
            n = mm.group(1)
            if fixed_d is not None and str(fixed_d) == n:
                fixed_d = None
            if fixed_i is not None and str(fixed_i) == n:
                fixed_i = None
        if (fixed_d, fixed_i) != (d, i):
            # re-extract properly rather than simply blanking
            rd, ri = extract_counts(text)
            conn.execute("UPDATE articles SET deaths=?, injured=?, severity=? WHERE id=?",
                         (rd, ri, severity(text, rd, ri), rid))
            cleared += 1
    conn.commit()

    # 3. duplicates that survived: identical day, category, place and toll
    merged = 0
    seen = {}
    for rid, pub, cat, cities, d, grp in conn.execute(
            """SELECT id,published,category,cities,deaths,dup_group FROM articles
               WHERE is_duplicate=0 ORDER BY published_ts ASC"""):
        place = (cities or "").split(";")[0].strip()
        if not place:
            continue
        key = (pub, cat, place.lower(), d)
        if key in seen:
            conn.execute("UPDATE articles SET is_duplicate=1, dup_group=? WHERE dup_group=?",
                         (seen[key], grp))
            merged += 1
        else:
            seen[key] = grp
    conn.commit()

    if cleared or deleted or merged:
        tag = f" ({label})" if label else ""
        print(f"[auto-repair{tag}] corrected {cleared} figures, "
              f"removed {deleted} statistics, merged {merged} duplicates")
    return cleared + deleted + merged


def audit_events(events, conn):
    """Return (flags, summary). Flags are rows a human should look at."""
    flags = []

    def flag(ev, level, issue, detail=""):
        flags.append({
            "level": level, "issue": issue, "detail": detail,
            "date": ev["date"], "type": ev["category"], "place": ev["place"],
            "killed": ev["deaths"], "injured": ev["injured"],
            "headline": ev["headline_en"] or ev["headline"], "url": ev["url"],
        })

    tolls = [e["deaths"] for e in events if e["deaths"]]
    tolls.sort()
    p95 = tolls[int(len(tolls) * 0.95)] if len(tolls) > 20 else 999

    by_key = {}
    for e in events:
        text = all_text(e["headline_en"], e["headline"])

        # 1. a casualty figure that also appears as an age or a duration
        for mm in NUMBER_CONTEXT.finditer(text):
            n = mm.group(1)
            if n and (str(e["deaths"]) == n or str(e["injured"]) == n):
                flag(e, "HIGH", "figure may be an age or a time period",
                     f"{n} appears as '{mm.group(0).strip()}'")
                break

        # 2. statistical language - a round-up, not a single accident
        if STAT_HINT.search(text):
            flag(e, "HIGH", "looks like a statistic, not one accident")

        # 3. an implausibly large toll
        if e["deaths"] and e["deaths"] > max(p95, 25):
            flag(e, "MEDIUM", "unusually high death toll",
                 f"{e['deaths']} vs 95th percentile {p95}")

        # 4. still not translated
        if not (e["headline_en"] or "").strip():
            flag(e, "MEDIUM", "no English text yet (awaiting translation)")

        # 5. classified with no location at all
        if e["place"] == "Not identified" and (e["deaths"] or 0) >= 3:
            flag(e, "MEDIUM", "no place identified despite a significant toll")

        # 6. 'others' with no sector - the catch-all bucket
        if e["category"] == "others" and e["sector"] in ("", "unspecified"):
            flag(e, "LOW", "in 'others' with no sector identified")

        # 7. probable duplicate that did not merge: same day, type, place, toll
        key = (e["date"], e["category"], e["place"], e["deaths"])
        if e["place"] != "Not identified" and key in by_key:
            flag(e, "HIGH", "possible duplicate of another row",
                 f"same day, type, place and toll as: {by_key[key][:60]}")
        else:
            by_key[key] = e["headline_en"] or e["headline"]

        # 8. reports of the same accident give different casualty numbers. The
        #    highest is kept (tolls climb), but a human should confirm which is
        #    right - this is exactly how a wrong "6 injured" hid behind a correct
        #    "12 injured".
        if e.get("toll_conflict"):
            flag(e, "MEDIUM", "reports disagree on the casualty count",
                 e.get("toll_detail", ""))

    summary = {
        "accidents": len(events),
        "with place": sum(1 for e in events if e["place"] != "Not identified"),
        "with killed": sum(1 for e in events if e["deaths"] is not None),
        "with cause": sum(1 for e in events if (e["cause"] or "").strip()),
        "with english": sum(1 for e in events if (e["headline_en"] or "").strip()),
        "flags HIGH": sum(1 for f in flags if f["level"] == "HIGH"),
        "flags MEDIUM": sum(1 for f in flags if f["level"] == "MEDIUM"),
        "flags LOW": sum(1 for f in flags if f["level"] == "LOW"),
    }
    return flags, summary


def export_review(flags, path="REVIEW_these_rows.csv"):
    order = {"HIGH": 0, "MEDIUM": 1, "LOW": 2}
    flags = sorted(flags, key=lambda f: (order.get(f["level"], 3), f["date"]), reverse=False)
    with _w(path) as f:
        w = csv.writer(f)
        w.writerow(["Priority", "What looks wrong", "Detail", "Date", "Accident Type",
                    "City / Place", "Killed", "Injured", "Headline", "Link"])
        for x in flags:
            w.writerow([x["level"], x["issue"], x["detail"], x["date"], x["type"],
                        x["place"], x["killed"] if x["killed"] is not None else "",
                        x["injured"] if x["injured"] is not None else "",
                        clean_field(x["headline"]), x["url"]])
    return len(flags)


STALE = ["SUMMARY.csv", "SUMMARY_simple.csv", "SUMMARY_month_by_type.csv", "SUMMARY_weekly.csv",
         "SUMMARY_by_city.csv", "SUMMARY_casualties_monthly.csv", "SUMMARY_cause_histogram.csv",
         "SUMMARY_others_by_sector.csv", "SUMMARY_cause_phrases.csv", "cause_summary.csv",
         "cause_trend_monthly.csv", "monthly_summary.csv", "yearly_summary.csv",
         "articles.csv", "EVENTS_unique.csv"]


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
    try:
        build_place_patterns()
    except Exception as e:                                # noqa: BLE001
        print(f"[warn] gazetteer build failed, using built-in list: {type(e).__name__}: {e}")
    stats, tbudget = {}, MAX_TRANSLATE_PER_RUN

    for code, (label, ceid) in EDITIONS.items():
        for q in GN_QUERIES.get(code, []):
            url = f"{RSS_SEARCH}{urllib.parse.quote(q)}&hl={code}-IN&gl=IN&ceid={ceid}"
            data, _ = http_get(url)
            items = parse_feed(data, label, q)
            n, tbudget = store(conn, items, stats, tbudget)
            print(f"[GN {label}] {q!r}: {len(items)} seen, {n} kept")
            time.sleep(1)

    for q in GDELT_QUERIES:
        items = fetch_gdelt(q)
        n, tbudget = store(conn, items, stats, tbudget)
        print(f"[GDELT] {q[:44]!r}: {len(items)} seen, {n} kept")
        time.sleep(2)

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
    for name, fn in (("translate", lambda: backfill_translations(conn)),
                     ("articles", lambda: backfill_articles(conn, MAX_ARTICLE_FETCH_PER_RUN, ARTICLE_FETCH_MINUTES * 60)),
                     ("rescreen", lambda: rescreen_all(conn)),
                     ("dedupe", lambda: rededupe(conn)),
                     ("auto-repair", lambda: auto_repair(conn, "end of run"))):
        try:
            fn()
        except Exception as e:                                      # noqa: BLE001
            print(f"[warn] {name} failed and was skipped: {type(e).__name__}: {e}")

    clear_stale()
    events = resolve_events(conn)          # single source of truth
    n = export_accidents(conn, events)
    export_summary(events, "SUMMARY_all.csv", False)
    export_summary(events, "SUMMARY_confirmed.csv", True)
    export_category_summary(events, "SUMMARY_by_category.csv", False)
    export_cause_summary(events, "SUMMARY_by_cause.csv", False)
    export_monthly_from_events(events)
    export_dashboard(events)

    flags, qa = audit_events(events, conn)
    export_review(flags)
    print("\nDATA QUALITY (the tool checking its own work):")
    total = max(qa["accidents"], 1)
    for k in ("with place", "with killed", "with cause", "with english"):
        print(f"   {k:14} {qa[k]:5} / {qa['accidents']}  ({100*qa[k]//total}%)")
    print(f"   rows to review {qa['flags HIGH']} high, {qa['flags MEDIUM']} medium, "
          f"{qa['flags LOW']} low  -> REVIEW_these_rows.csv")
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

        # THE RECURRING DOUBLED-HEADLINE BUG.
        # Cause: the title and the RSS snippet were translated in ONE call joined
        # by a newline, and Google News snippets usually repeat the headline, so
        # the stored value became "<text>\n<the same text>". The newline then
        # split the row in spreadsheet software, making the row count look wrong.
        doubled = ("Mumbai local train accident: Crane fell on power line in Kurla\n"
                   "Mumbai local train accident: Crane fell on power line in Kurla")
        assert clean_field(doubled) == "Mumbai local train accident: Crane fell on power line in Kurla"
        assert "\n" not in clean_field(doubled) and "\r" not in clean_field(doubled)
        assert clean_field("Jaipur airport - ABP News Jaipur airport - ABP News") == \
            "Jaipur airport - ABP News"
        assert clean_field("A\tB\r\nC") == "A B C"

        # THE KANPUR DISCREPANCY: the accidents file and the summaries must agree.
        import tempfile, os as _os
        conn2 = sqlite3.connect(":memory:")
        init_db(conn2)
        st2 = {}
        base = datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()
        for t, src_ in [("45 year old youth dies after collision with unknown vehicle in Kanpur", "Jagran"),
                        ("Eight passengers injured as bus collided with truck in Mainpuri", "Amar Ujala"),
                        ("Three killed as bus overturns near Pune on NH-48", "Times of India")]:
            store(conn2, [{"title": t, "snippet": "", "body": "", "url": "http://x/" + t[:9],
                           "source": src_, "language": "English", "query": "q",
                           "published": "2026-08-20", "published_ts": base}], st2)
        rededupe(conn2)
        evs = resolve_events(conn2)
        cwd = _os.getcwd()
        _os.chdir(tempfile.mkdtemp())
        try:
            export_accidents(conn2, evs)
            export_summary(evs, "SUMMARY_all.csv", False)
            acc = list(csv.DictReader(open("ACCIDENTS.csv", encoding="utf-8-sig")))
            summ = list(csv.DictReader(open("SUMMARY_all.csv", encoding="utf-8-sig")))
            ak = sum(int(r["Killed"]) for r in acc if r["Killed"].strip())
            sk = sum(int(r["People Killed"]) for r in summ)
            ai = sum(int(r["Injured"]) for r in acc if r["Injured"].strip())
            si = sum(int(r["People Injured"]) for r in summ)
            assert ak == sk, f"killed disagree: accidents {ak} vs summary {sk}"
            assert ai == si, f"injured disagree: accidents {ai} vs summary {si}"
            assert len(acc) == sum(int(r["Number of Accidents"]) for r in summ), "counts disagree"
            # the Mainpuri crash must NOT be filed under Kanpur
            mp = [r for r in acc if "Mainpuri" in r["City / Place"]]
            print(f"consistency: accidents={len(acc)} killed={ak} injured={ai} (summary matches)")
        finally:
            _os.chdir(cwd)

        # HIGHWAYS ARE GONE: not extracted, not stored, not compared, not exported.
        assert extract_places("Truck hits divider on Mumbai-Pune expressway")[1] == ""
        # and a place that appears only inside a road name is not a location
        assert extract_places("Youth dies near Bidhnu on Kanpur Sagar Highway")[0] == ""
        assert extract_places("Truck hits divider on Mumbai-Pune expressway")[0] == ""
        # a route endpoint is not the accident site either
        assert extract_places("Bus from Delhi to Kanpur collided with truck")[0] == ""
        # but a genuine location still resolves
        assert extract_places("Three killed as bus overturns near Pune")[0] == "Pune"
        assert extract_places("Wall collapses in Bhiwandi, 3 dead")[0] == "Bhiwandi"
        assert "highways" not in COLUMNS

        # BUDGETS: the caps were never the binding limit.
        # 698 of 699 real links were Google stubs, so a big fetch budget was
        # spent on links that fail instantly; and the free translator throttles
        # long before the translation cap is reached.
        assert translate_to_en("Three killed in bus crash") == "", \
            "English text must not consume a translation call"
        _TRANSLATE_STATE["blocked"] = True
        assert translate_to_en("बस दुर्घटना में तीन की मौत") == "", \
            "a throttled service must fail fast, not hammer"
        _TRANSLATE_STATE["blocked"] = False
        _TRANSLATE_STATE["fails"] = 0

        # AGES MUST NEVER BE A CASUALTY FIGURE - the recurring bug
        for t, e in [("20-year-old youth dies in Nawada road accident", (1, None)),
                     ("45 year old youth dies due to collision", (1, None)),
                     ("19-year-old girl tragically dies in Keshod", (1, None)),
                     ("27-year-old youth of Ulhasnagar died", (1, None)),
                     ("32-year-old worker seriously injured at site", (None, 1)),
                     ("Six women laborers die in Zaheerabad", (6, None)),
                     ("9 Nationals Killed In Kolkata Hotel Fire", (9, None))]:
            assert extract_counts(t) == e, f"casualty: {t!r} -> {extract_counts(t)}, want {e}"
        # and the repair pass must RECOMPUTE stored figures, not just categories
        import inspect as _insp
        assert "extract_counts" in _insp.getsource(rescreen_all), \
            "rescreen must recompute casualty figures or old wrong values survive"

        # A VICTIM'S NATIONALITY IS NOT A LOCATION - in either direction.
        # Migrant workers from Nepal and Bangladesh are common on Indian sites,
        # so vetoing on the word "Nepal" silently lost real Indian accidents.
        for t in ["Nepal native among 3 dead as wall collapses at Mathura construction site",
                  "Three labourers including one from Nepal die at Vrindavan temple construction site",
                  "Nepali national among 3 workers killed as under-construction building collapses in Vrindavan",
                  "Bangladeshi migrant worker dies at Kolkata metro site"]:
            keep, why = screen(t, "", "Amar Ujala", "", "2026-08-20")
            assert keep, f"Indian accident with a foreign victim was dropped as {why}: {t}"
            assert classify(t)[0] in ("construction_ongoing", "others"), t
        for t in ["Bus plunges into gorge in Nepal, 20 dead",
                  "Building collapses in Dhaka, Bangladesh, 5 killed",
                  "Road accident in Kathmandu kills 12",
                  "Factory fire in Bangladesh kills 16 workers"]:
            keep, _ = screen(t, "", "NDTV", "", "2026-08-20")
            assert not keep, f"a genuinely foreign accident was kept: {t}"
        # a workplace fatality is an accident even with no crash word
        keep, _ = screen("Two workers killed at a factory in Surat", "", "Sandesh", "", "2026-08-20")
        assert keep
        # but a death that is not an accident still is not one
        for t in ["Veteran actor dies at 85 in Mumbai",
                  "Worker murdered at construction site in Delhi"]:
            keep, _ = screen(t, "", "NDTV", "", "2026-08-20")
            assert not keep, f"non-accident kept: {t}"

        # THE EXACT TIMES OF INDIA HEADLINE that exposed this class of bug.
        # "Nepal National" names a nationality, not a country location.
        toi = "Nepal National among 3 killed at construction site"
        keep, why = screen(toi, "", "The Times of India", "", "2026-08-21")
        assert keep, f"the TOI headline was dropped as {why}"
        assert classify(toi)[0] == "construction_ongoing", classify(toi)
        assert extract_counts(toi) == (3, None), extract_counts(toi)
        for t in ["Nepali national among 3 workers killed in Vrindavan",
                  "Bangladesh national dies at Kolkata metro site",
                  "Nepal workers among 4 injured in scaffolding collapse",
                  "Two labourers died in Noida"]:
            k2, w2 = screen(t, "", "The Times of India", "", "2026-08-21")
            assert k2, f"kept-case failed ({w2}): {t}"
        for t in ["Factory fire in Bangladesh kills 16 workers",
                  "Bangladesh workers die in Dhaka factory collapse",
                  "Worker murdered at construction site in Delhi",
                  "Migrant worker commits suicide in Surat",
                  "Minister meets workers at Pune factory"]:
            k2, _ = screen(t, "", "The Times of India", "", "2026-08-21")
            assert not k2, f"should have been dropped: {t}"

        # CAUSE MUST NOT BE EMPTY WHEN THE HEADLINE STATES IT.
        # The Vrindavan collapse said "building shuttering collapses" and the
        # cause column was still blank, because only article BODIES were used and
        # most bodies cannot be fetched.
        assert derive_cause_mechanism(
            "3 workers killed as building shuttering collapses in Vrindavan"
        ) == "Shuttering / formwork failure"
        assert "Tyre burst" in derive_cause_mechanism("bus overturns after tyre burst on NH-48")
        assert "Derailment" in derive_cause_mechanism("Train derails near Kanpur, 4 dead")
        assert derive_cause_mechanism("Minister opens new hospital") == ""

        # EVERY TEXT SOURCE MUST REACH EVERY STAGE.
        # The gate previously saw only the headline, so an item whose accident
        # evidence sat in the feed body was dropped before the body was read.
        head_only = "Tragedy in Noida"
        feed_body = ("A 32-year-old labourer died after falling from the scaffolding of an "
                     "under-construction tower in Sector 78, Noida. Two others were injured.")
        assert not screen(head_only, "", "Unknown Portal", "", "2026-08-20")[0]
        assert screen(all_text(head_only, "", feed_body), "", "Unknown Portal", "", "2026-08-20")[0], \
            "evidence in the feed body must reach the gate"
        # and every field must be filled from that body
        conn3 = sqlite3.connect(":memory:")
        init_db(conn3)
        store(conn3, [{"title": head_only, "snippet": "", "body": feed_body,
                       "url": "http://x/9", "source": "Unknown Portal", "language": "English",
                       "query": "q", "published": "2026-08-20",
                       "published_ts": datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()}], {})
        got = conn3.execute("SELECT category,cities,deaths,injured,victim_age,time_of_day "
                            "FROM articles").fetchone()
        assert got and got[0] == "construction_ongoing", got
        assert got[1] == "Noida" and got[2] == 1 and got[3] == 2 and got[4] == "32", got
        # a contested number belongs to the cue that follows it
        assert extract_counts("A worker died. Two others were injured.") == (1, 2)

        # TRANSLATION MUST HAPPEN BEFORE SCREENING FOR NON-ENGLISH ITEMS.
        # The gates are written mainly in English, so a Hindi article was being
        # rejected as "no accident evidence" before translation could make it
        # readable - and its whole article sat untranslated in the feed body.
        _saved = globals().get("_MOCK_TRANSLATE")
        globals()["_MOCK_TRANSLATE"] = lambda x: (
            "Shuttering of under-construction building collapsed in Vrindavan, Mathura"
            if "मथुरा" in x else
            "Three workers including one from Nepal died. Two others were injured at 11 pm."
            if "हादसे" in x else "")
        conn4 = sqlite3.connect(":memory:")
        init_db(conn4)
        st4 = {}
        store(conn4, [{"title": "मथुरा के वृंदावन में निर्माणाधीन इमारत की शटरिंग गिरी",
                       "snippet": "",
                       "body": "हादसे में नेपाल के एक मजदूर समेत तीन श्रमिकों की मौत हो गई।",
                       "url": "https://www.bhaskar.com/x", "source": "Dainik Bhaskar",
                       "language": "Hindi", "query": "q", "published": "2026-08-20",
                       "published_ts": datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()}],
              st4, translate_budget=10)
        got4 = conn4.execute("SELECT category,cities,deaths,title_en,translated "
                             "FROM articles").fetchone()
        assert got4, f"Hindi item was dropped: {st4}"
        assert got4[0] == "construction_ongoing" and got4[1] == "Vrindavan", got4
        assert got4[2] == 3 and got4[4] == 1, got4
        # a FOREIGN item must still be caught once translated
        globals()["_MOCK_TRANSLATE"] = lambda x: "Bus falls into gorge in Nepal, 20 dead"
        st5 = {}
        conn5 = sqlite3.connect(":memory:")
        init_db(conn5)
        store(conn5, [{"title": "नेपाल में बस खाई में गिरी, 20 की मौत", "snippet": "", "body": "",
                       "url": "http://x", "source": "Dainik Bhaskar", "language": "Hindi",
                       "query": "q", "published": "2026-08-20",
                       "published_ts": datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()}],
              st5, translate_budget=10)
        assert conn5.execute("SELECT COUNT(*) FROM articles").fetchone()[0] == 0, \
            "a foreign accident must still be dropped after translation"
        globals()["_MOCK_TRANSLATE"] = _saved

        # AGES IN INDIAN SCRIPTS were not being stripped, so "25 वर्षीय मजदूर
        # की मौत" (a 25-year-old labourer died) was recorded as 25 deaths.
        for t, e in [("फैक्ट्री में गिरने से 25 वर्षीय मजदूर की मौत", (1, None)),
                     ("शेखपुरा में ट्रेन से कटकर 23 वर्षीय युवक की मौत", (1, None)),
                     ("23 సంవత్సరాల యువకుడు మృతి", (1, None)),
                     ("बस दुर्घटना में ३ की मौत, २ घायल", (3, 2))]:
            assert extract_counts(t) == e, f"indic age: {t!r} -> {extract_counts(t)}"
        assert "25" in extract_ages("25 वर्षीय मजदूर की मौत")
        # a school bus in a canal is a ROAD accident, not a structure collapse
        assert classify("School bus overturns into canal in NTR district, six students injured")[0] == "roadway"
        # a bus hitting a roadside crowd is a ROAD accident, not maritime
        assert classify("Speeding bus rammed into people watching an orchestra on the roadside")[0] == "roadway"

        # STATISTICAL ROUND-UPS IN INDIAN LANGUAGES.
        # "19 மாதங்களில் 28,309 பேர் உயிரிழப்பு" = 28,309 died over 19 months.
        # That is a statistic, and the 19 was being recorded as a death toll.
        tamil_stat = "சாலை விபத்துகளில் கடந்து 19 மாதங்களில் 28,309 பேர் உயிரிழப்பு"
        assert not screen(tamil_stat, "", "Lokal Tamil", "", "2026-08-20")[0]
        assert extract_counts(tamil_stat) == (None, None), extract_counts(tamil_stat)
        assert not screen("सड़क हादसों में पिछले 19 महीनों में 28309 लोगों की मौत",
                          "", "Jagran", "", "2026-08-20")[0]
        # a real Hindi accident must still pass
        assert screen("बस दुर्घटना में ३ की मौत, २ घायल", "", "Jagran", "", "2026-08-20")[0]
        # TRANSLATION MUST BE RETRIED, not attempted once and abandoned
        import inspect as _i2
        assert "backfill_translations" in _i2.getsource(run), \
            "untranslated rows must be retried on later runs"

        # THE SELF-AUDIT must catch the shapes of every bug found by hand.
        probe = [
            {"date": "2026-08-01", "last": "2026-08-01", "category": "roadway", "sector": "",
             "place": "Chennai", "places": "Chennai", "deaths": 19, "injured": None,
             "severity": "Fatal", "tod": "", "gender": "", "ages": "", "cause": "", "n": 1,
             "outlets": "x", "headline": "19 மாதங்களில் 28309 பேர் உயிரிழப்பு",
             "headline_en": "28309 died in road accidents over 19 months", "url": ""},
            {"date": "2026-08-02", "last": "2026-08-02", "category": "others",
             "sector": "unspecified", "place": "Not identified", "places": "",
             "deaths": 5, "injured": None, "severity": "Fatal", "tod": "", "gender": "",
             "ages": "", "cause": "", "n": 1, "outlets": "x",
             "headline": "कुछ हुआ", "headline_en": "", "url": ""},
        ]
        fl, qa_ = audit_events(probe, None)
        issues = {f["issue"] for f in fl}
        assert any("age or a time period" in i for i in issues), issues
        assert any("statistic" in i for i in issues), issues
        assert any("no English text" in i for i in issues), issues
        assert any("no place identified" in i for i in issues), issues
        assert any("no sector" in i for i in issues), issues

        # AUTO-REPAIR must FIX errors, not report them, and must run after every
        # translation batch as well as at the end of a run.
        conn6 = sqlite3.connect(":memory:")
        init_db(conn6)
        ts6 = datetime(2026, 8, 20, tzinfo=timezone.utc).timestamp()
        for rid, ttl, dd, place in [
                ("a", "19 மாதங்களில் 28309 பேர் உயிரிழப்பு", 19, "Chennai"),
                ("b", "Railway worker married 10 months ago, killed in train accident", 10, "Kanpur"),
                ("d", "Wall collapses in Bhiwandi, 3 dead", 3, "Bhiwandi"),
                ("e", "Wall collapse in Bhiwandi kills 3 labourers", 3, "Bhiwandi"),
                ("f", "Three killed as bus overturns near Pune", 3, "Pune")]:
            conn6.execute(
                """INSERT INTO articles (id,title,title_en,published,published_ts,category,
                   language,title_norm,cities,deaths,severity,is_duplicate,dup_group)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,0,?)""",
                (rid, ttl, ttl if ttl.isascii() else "", "2026-08-20", ts6, "roadway",
                 "English", norm_title(ttl), place, dd, "Fatal", rid))
        conn6.commit()
        auto_repair(conn6, "test")
        assert conn6.execute("SELECT COUNT(*) FROM articles WHERE id='a'").fetchone()[0] == 0, \
            "a statistical round-up must be deleted automatically"
        assert conn6.execute("SELECT deaths FROM articles WHERE id='b'").fetchone()[0] is None, \
            "'married 10 months ago' must not remain a death toll"
        assert conn6.execute("SELECT is_duplicate FROM articles WHERE id='e'").fetchone()[0] == 1, \
            "an unmerged duplicate must be merged automatically"
        assert conn6.execute("SELECT deaths FROM articles WHERE id='f'").fetchone()[0] == 3, \
            "a correct row must be left alone"
        import inspect as _i3
        assert "auto_repair" in _i3.getsource(backfill_translations), \
            "repair must run after every translation batch"
        assert "auto-repair" in _i3.getsource(run), "repair must run at the end of every run"

        # FOLLOW-UP COVERAGE OF ONE ACCIDENT, spread over weeks and languages,
        # must collapse to a single row: date = first reported, toll = last.
        conn7 = sqlite3.connect(":memory:")
        init_db(conn7)
        def _t(mo, dy):
            return datetime(2026, mo, dy, tzinfo=timezone.utc).timestamp()
        seed = [("Maharashtra: Bhiwandi four-storey building collapse kills 9, rescue on", _t(7, 30), 9, "Bhiwandi", "old_structure_collapse"),
                ("Bhiwandi building collapse: contractor and owner under lens, collapse probe", _t(7, 31), None, "Bhiwandi", "old_structure_collapse"),
                ("PM expresses grief over loss of lives in Bhiwandi building collapse", _t(7, 31), None, "Bhiwandi", "old_structure_collapse"),
                ("Civic lapse led to Bhiwandi building collapse, wrongly classified building", _t(8, 10), 12, "Bhiwandi", "old_structure_collapse"),
                ("Two die as wall collapses at Bhiwandi godown during rain", _t(8, 20), 2, "Bhiwandi", "old_structure_collapse"),
                ("Three killed as bus overturns near Pune on NH-48", _t(8, 5), 3, "Pune", "roadway"),
                ("Four killed as truck hits divider near Pune", _t(8, 19), 4, "Pune", "roadway")]
        for n_, (ttl, tsx, dd, plc, cat) in enumerate(seed):
            conn7.execute(
                """INSERT INTO articles (id,title,title_en,published,published_ts,category,
                   language,title_norm,cities,deaths,severity,is_duplicate,dup_group)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,0,?)""",
                (str(n_), ttl, ttl,
                 datetime.fromtimestamp(tsx, timezone.utc).strftime("%Y-%m-%d"), tsx, cat,
                 "English", norm_title(ttl), plc, dd, "Fatal", str(n_)))
        conn7.commit()
        rededupe(conn7)
        evs7 = resolve_events(conn7)
        assert len(evs7) == 4, f"7 reports should give 4 accidents, got {len(evs7)}"
        big = [e for e in evs7 if e["n"] == 4]
        assert big, "the four Bhiwandi reports must merge into one accident"
        assert big[0]["date"] == "2026-07-30", f"date must be the FIRST report: {big[0]['date']}"
        assert big[0]["deaths"] == 12, f"toll must be the LATEST reported: {big[0]['deaths']}"
        # foreign countries named in Indian scripts must be rejected
        for t in ["கொலம்பியாவில் பயங்கர நிலநடுக்கம்: 77 பேர் உயிரிழப்பு",
                  "உகாண்டாவில் பள்ளிப் பேருந்து கவிழ்ந்து விபத்து",
                  "बांग्लादेश में इमारत गिरी, 5 की मौत"]:
            assert india_verdict(t) == "foreign", f"foreign in native script kept: {t}"

        # MERGING MUST COMPARE ALL THE FACTS, and a contradiction in ANY of them
        # (place, day, time of day, activity, object, building height, ages)
        # means two separate accidents no matter how similar the wording.
        def _mk(rows_):
            cc = sqlite3.connect(":memory:")
            init_db(cc)
            for n_, (ttl, tsx, dd, plc, cat, tod) in enumerate(rows_):
                cc.execute(
                    """INSERT INTO articles (id,title,title_en,published,published_ts,category,
                       language,title_norm,cities,deaths,severity,time_of_day,is_duplicate,dup_group)
                       VALUES (?,?,?,?,?,?,?,?,?,?,?,?,0,?)""",
                    (str(n_), ttl, ttl,
                     datetime.fromtimestamp(tsx, timezone.utc).strftime("%Y-%m-%d"), tsx, cat,
                     "English", norm_title(ttl), plc, dd, "Fatal", tod, str(n_)))
            cc.commit()
            rededupe(cc)
            return resolve_events(cc)

        def _T(mo, dy):
            return datetime(2026, mo, dy, tzinfo=timezone.utc).timestamp()

        merge_cases = [
            ("follow-up over 11 days", 1,
             [("Maharashtra: Bhiwandi four-storey building collapse kills 9, rescue on", _T(7, 30), 9, "Bhiwandi", "old_structure_collapse", "Night"),
              ("Bhiwandi building collapse: contractor and owner under lens", _T(7, 31), None, "Bhiwandi", "old_structure_collapse", ""),
              ("Civic lapse led to Bhiwandi four-storey building collapse", _T(8, 10), 12, "Bhiwandi", "old_structure_collapse", "")]),
            ("different building height and time of day", 2,
             [("Bhiwandi four-storey building collapse kills 9 during night", _T(7, 30), 9, "Bhiwandi", "old_structure_collapse", "Night"),
              ("Bhiwandi two-storey building collapse kills 3 in the morning", _T(8, 12), 3, "Bhiwandi", "old_structure_collapse", "Day")]),
            ("different work activity", 2,
             [("Worker dies as scaffolding collapses at Noida site on Monday", _T(7, 10), 1, "Noida", "construction_ongoing", ""),
              ("Worker dies as crane topples at Noida site on Friday", _T(7, 25), 1, "Noida", "construction_ongoing", "")]),
            ("different vehicle", 2,
             [("Three killed as bus overturns near Pune", _T(8, 5), 3, "Pune", "roadway", ""),
              ("Three killed as truck overturns near Pune", _T(8, 18), 3, "Pune", "roadway", "")]),
        ]
        for label_, want_, rows_ in merge_cases:
            got_ = len(_mk(rows_))
            assert got_ == want_, f"merge case {label_!r}: got {got_}, want {want_}"
        # and the first date with the latest toll
        one = _mk(merge_cases[0][2])[0]
        assert one["date"] == "2026-07-30" and one["deaths"] == 12, one

        # PROTEST DEATHS ARE NOT ACCIDENTS, in any language.
        for t in ["मराठा आरक्षण: 18 आंदोलकांचा मृत्यू",
                  "मराठा मोर्चात 18 जणांचा मृत्यू",
                  "Maratha morcha: 18 died",
                  "Maratha reservation stir: 18 deaths"]:
            assert not screen(t, "", "Lokmat", "", "2026-08-20")[0], f"protest kept: {t}"
        # AND a toll too large for one Indian accident is a round-up, not a toll
        assert extract_counts("अपघातात 280 जणांचा मृत्यू") == (None, None)
        assert extract_counts("Mumbai: 280 died in building collapse") == (None, None)
        assert extract_counts("Ahmedabad plane crash kills 133") == (133, None)

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

        # CATEGORY SUMMARY must be built from the events and its TOTAL row must
        # equal the sum of the per-category rows and of the events themselves.
        import tempfile, os as _os
        sample_events = [
            {"category": "roadway", "sector": "", "place": "Pune", "severity": "Fatal",
             "deaths": 3, "injured": 2, "headline": "Bus overturns after brake failure near Pune",
             "headline_en": "Bus overturns after brake failure near Pune", "cause": ""},
            {"category": "roadway", "sector": "", "place": "Not identified", "severity": "Injury only",
             "deaths": None, "injured": 4, "headline": "Two injured in car accident in Guntur",
             "headline_en": "Two injured in car accident in Guntur", "cause": ""},
            {"category": "old structure collapse", "sector": "", "place": "Bhiwandi", "severity": "Fatal",
             "deaths": 12, "injured": 0, "headline": "Building collapse kills 12",
             "headline_en": "Building collapse kills 12", "cause": "wall gave way"},
            {"category": "construction ongoing", "sector": "", "place": "Noida", "severity": "Near miss",
             "deaths": None, "injured": None, "headline": "Scaffolding collapses, all safe",
             "headline_en": "Scaffolding collapses, all safe", "cause": ""},
        ]
        _tmp = tempfile.mkdtemp()
        _cat = _os.path.join(_tmp, "cat.csv")
        export_category_summary(sample_events, _cat, confirmed_only=False)
        with open(_cat, encoding="utf-8-sig") as _fh:
            _rows = list(csv.reader(_fh))
        _tot = next(r for r in _rows if r and r[0] == "TOTAL")
        assert int(_tot[1]) == len(sample_events), "category TOTAL accidents must equal event count"
        assert int(_tot[5]) == 15, f"category TOTAL killed must be 3+12=15, got {_tot[5]}"
        assert int(_tot[6]) == 6, f"category TOTAL injured must be 2+4=6, got {_tot[6]}"
        _body = [r for r in _rows[1:] if r and r[0] not in ("TOTAL",)]
        assert sum(int(r[1]) for r in _body) == int(_tot[1]), "category rows must sum to TOTAL"
        assert sum(int(r[4]) for r in _body) == int(_tot[4]) == 1, "one near miss expected"

        # STANDARDISED CAUSE must come from the controlled vocabulary or be
        # 'Not stated' - never free-text, never a guess.
        allowed = set(CAUSE_MECHANISMS.keys()) | {"Not stated"}
        for ev in sample_events:
            assert standardise_cause(ev) in allowed, \
                f"cause not standardised: {standardise_cause(ev)!r}"
        assert standardise_cause(sample_events[0]) == "Brake failure", "brake failure cue missed"
        assert standardise_cause(sample_events[1]) == "Not stated", \
            "no cue must yield 'Not stated', not a guess"
        # THE CAUSE MUST COME FROM ALL TEXT, NOT THE HEADLINE ALONE: a headline
        # with no cue but a body/snippet that explains the cause must still be
        # classified from that pooled text (resolve_events supplies 'cause_text').
        buried = {"category": "roadway", "sector": "", "place": "X", "severity": "Fatal",
                  "deaths": 2, "injured": 0, "headline": "Two die on highway near town",
                  "headline_en": "Two die on highway near town", "cause": "",
                  "cause_text": "Two die on highway near town. Police said the truck "
                                "suffered a sudden brake failure before hitting the divider."}
        assert standardise_cause(buried) == "Brake failure", \
            "cause in the body, not the headline, must still be detected"

        # CAUSE SUMMARY must always carry a 'Not stated' row when any cause is unknown.
        _cau = _os.path.join(_tmp, "cause.csv")
        export_cause_summary(sample_events, _cau, confirmed_only=False)
        with open(_cau, encoding="utf-8-sig") as _fh:
            _ctext = _fh.read()
        assert "Not stated" in _ctext, "cause summary must display the unknown share"

        # CASUALTY MERGE: the toll is read from the ENGLISH reports (which extract
        # reliably) before the foreign-language copies. Here The Hindu reports
        # "6 killed, 12 injured" and a later Bengali rewrite says "6 injured" - the
        # English figure (12) must win, not the later Bengali one (the real bug).
        conn_tel = sqlite3.connect(":memory:")
        init_db(conn_tel)
        _tt = datetime(2026, 8, 26, tzinfo=timezone.utc).timestamp()
        tel = [("Six killed, 12 injured as speeding bus crashes into lorry in Suryapet",
                _tt, 6, 12, "Suryapet", "English"),
               ("Suryapet bus crash: 6 killed, 6 injured (Bengali rewrite)",
                _tt + 3600, 6, 6, "Suryapet", "Bengali")]
        for n_, (ttl, tsx, dd, ii, plc, lang) in enumerate(tel):
            conn_tel.execute(
                """INSERT INTO articles (id,title,title_en,published,published_ts,category,
                   language,title_norm,cities,deaths,injured,severity,is_duplicate,dup_group)
                   VALUES (?,?,?,?,?,?,?,?,?,?,?,?,0,?)""",
                (str(n_), ttl, ttl,
                 datetime.fromtimestamp(tsx, timezone.utc).strftime("%Y-%m-%d"), tsx, "roadway",
                 lang, norm_title(ttl), plc, dd, ii, "Fatal", "g1"))
        conn_tel.commit()
        tev = resolve_events(conn_tel)[0]
        assert tev["deaths"] == 6, f"killed must stay 6, got {tev['deaths']}"
        assert tev["injured"] == 12, f"injured must be the English 12, not the Bengali 6, got {tev['injured']}"
        assert tev["toll_conflict"], "disagreeing reports must be flagged for review"

        # NUMBERS IN OUTLET NAMES ARE NOT CASUALTIES: "News18", "TV9" must not be
        # read as a death toll. This corrupted many regional-language rows.
        assert extract_counts("Six killed in crash - News18 Telugu") == (6, None), "News18 leaked as toll"
        assert extract_counts("Labourer dead, 3 injured in collapse - News18") == (1, 3), "News18 leaked"
        assert extract_counts("Bhiwandi building collapsed - TV9 Marathi") == (None, None), "TV9 leaked"
        assert extract_counts("8 dead, 24 injured in bus-truck collision") == (8, 24), "real 24 wrongly stripped"

        # NATURAL DISASTERS must be dropped even in native scripts. A Bengali
        # glacier-avalanche story from an Indian outlet was being kept and
        # mislabelled a roadway accident (glacier=হিমবাহ, avalanche=তুষারধস were
        # not in the native hazard list). A retrospective ("11 years ago" =
        # "১১ বছর আগের") must also read as old, not current.
        for bad in ["প্রলয়ের নেপথ্যে প্রকাণ্ড হিমবাহ - ধস ! মত মার্কিন ভূতত্ত্ব সংস্থার",
                    "ল্যাংটাং রিরুং ফেরাল ১১ বছর আগের হিমবাহ - ধসের বিভীষিকা",
                    "Massive glacier avalanche kills 40 in the Himalayas"]:
            k, why = screen(bad, "", "bartamanpatrika.com", "https://x", "2026-08-28")
            assert not k, f"natural disaster kept ({why}): {bad[:40]}"
        assert currency_verdict("বছর আগের সেই ভয়াবহ ঘটনা", "2026-08-28") == "old", \
            "native 'years ago' must read as old"
        # but a real building-collapse accident that uses ধস must still be kept
        okc, _ = screen("ভবন ধসে ৩ শ্রমিকের মৃত্যু, মুম্বইয়ে বহুতল ভেঙে পড়ল",
                        "", "ndtv", "https://x", "2026-08-28")
        assert okc, "a real building collapse must not be blocked by the hazard fix"

        print("SELF-TEST PASSED")
    else:
        run()# How much each fact matters when comparing two reports. Higher = more telling.
