#!/usr/bin/env python3
"""
India Accident News Monitor  (v4)
=================================

Collects INFRASTRUCTURE / TRANSPORT accident news for India from:
  (A) Google News RSS across 10 Indian-language editions, and
  (B) direct newspaper RSS feeds (NEWSPAPER_FEEDS).

Then it: filters OUT natural calamities, classifies each item into a specific
category, OPTIONALLY translates non-English items to English (to match numbers &
places across languages), de-duplicates across languages, extracts image links,
cities, highways and casualty counts, and writes monthly / yearly totals.

CATEGORIES (each is a column in the summaries)
  construction_infra  buildings, bridges, flyovers, tunnels, ports, dams, cranes,
                      scaffolding, walls/slabs, under-construction structures
  industrial          factory / boiler / gas-leak / plant / mine accidents
  pedestrian          people run over / hit while on foot
  traffic             cars, two-wheelers, autos - general road accidents
  bus                 bus accidents
  cargo               truck / lorry / tanker / trailer / goods-vehicle accidents
  train               train / rail / derailment
  flight              plane / helicopter / aviation

EXCLUDED: floods, landslides, cloudbursts, earthquakes, cyclones, lightning,
avalanches, tsunamis, wildfires, etc. (see NATURAL_CUES). Controlled by
STRICT_NATURAL_EXCLUSION.

TRANSLATION (optional, for cross-language dedup)
  Non-English titles are translated to English so the SAME English extractors
  (city list, casualty words) apply uniformly, and duplicates in Hindi/Tamil/etc.
  collapse into one event. It is CACHED (each item translated once) and CAPPED
  per run. If translation fails, the tool falls back to the digit/keyword method
  (casualty numbers already work without translation via Indic-digit conversion).
  Backend "builtin" translates via Google's free endpoint using ONLY the standard
  library - nothing to install. Set TRANSLATE_BACKEND="none" to switch it off.

HONESTY: counts are NEWS MENTIONS not official totals (MoRTH/NCRB/DGFASLI are
authoritative); non-English keyword sets are a starting point; images are stored
as links (publisher copyright); newspaper feed URLs break and are skipped+logged.

Standard library only. No pip install. No paid services.
"""

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
from collections import Counter, OrderedDict
from datetime import datetime, timezone
from difflib import SequenceMatcher
from email.utils import parsedate_to_datetime
from xml.etree import ElementTree

# ===========================================================================
# CONFIG
# ===========================================================================
EDITIONS = {
    "en": ("English", "IN:en"), "hi": ("Hindi", "IN:hi"), "bn": ("Bengali", "IN:bn"),
    "mr": ("Marathi", "IN:mr"), "ta": ("Tamil", "IN:ta"), "te": ("Telugu", "IN:te"),
    "kn": ("Kannada", "IN:kn"), "ml": ("Malayalam", "IN:ml"), "gu": ("Gujarati", "IN:gu"),
    "pa": ("Punjabi", "IN:pa"),
}

# Broad accident queries per language. Fine-grained category is decided later by
# detect_category, so these just need to surface accident stories.
GN_QUERIES = {
    "en": ['building OR bridge OR flyover collapse India', 'road OR highway accident India killed',
           'bus OR truck OR tanker accident India', 'train OR rail accident India derailment',
           'plane OR helicopter crash India', 'factory OR industrial accident India',
           'pedestrian killed road India'],
    "hi": ['इमारत OR पुल ढहा', 'सड़क हादसा मौत', 'बस OR ट्रक दुर्घटना', 'ट्रेन हादसा',
           'विमान हादसा', 'फैक्ट्री हादसा'],
    "bn": ['ভবন ধস', 'সড়ক দুর্ঘটনা নিহত', 'বাস OR ট্রেন দুর্ঘটনা', 'কারখানা দুর্ঘটনা'],
    "mr": ['इमारत कोसळली', 'रस्ता अपघात मृत्यू', 'बस OR रेल्वे अपघात', 'कारखाना अपघात'],
    "ta": ['கட்டிடம் இடிந்து', 'சாலை விபத்து உயிரிழப்பு', 'பேருந்து OR ரயில் விபத்து', 'தொழிற்சாலை விபத்து'],
    "te": ['భవనం కూలింది', 'రోడ్డు ప్రమాదం మృతి', 'బస్సు OR రైలు ప్రమాదం', 'ఫ్యాక్టరీ ప్రమాదం'],
    "kn": ['ಕಟ್ಟಡ ಕುಸಿತ', 'ರಸ್ತೆ ಅಪಘಾತ ಸಾವು', 'ಬಸ್ OR ರೈಲು ಅಪಘಾತ', 'ಕಾರ್ಖಾನೆ ಅಪಘಾತ'],
    "ml": ['കെട്ടിടം തകർന്നു', 'റോഡ് അപകടം മരണം', 'ബസ് OR ട്രെയിൻ അപകടം', 'ഫാക്ടറി അപകടം'],
    "gu": ['ઇમારત ધરાશાયી', 'માર્ગ અકસ્માત મોત', 'બસ OR ટ્રેન અકસ્માત', 'ફેક્ટરી અકસ્માત'],
    "pa": ['ਇਮਾਰਤ ਢਹਿ', 'ਸੜਕ ਹਾਦਸਾ ਮੌਤ', 'ਬੱਸ OR ਰੇਲ ਹਾਦਸਾ', 'ਫੈਕਟਰੀ ਹਾਦਸਾ'],
}

# Direct newspaper feeds (general -> filtered for accidents). Feeds break; dead
# ones are skipped and logged. Add regional/no-Google-News-edition papers here.
NEWSPAPER_FEEDS = [
    ("English", "https://indianexpress.com/feed/"),
    ("English", "https://www.thehindu.com/news/national/feeder/default.rss"),
    ("English", "https://feeds.feedburner.com/ndtvnews-india-news"),
    ("English", "https://www.news18.com/rss/india.xml"),
    ("Hindi",   "https://feed.livehindustan.com/rss/3127"),
    # ("Assamese", "https://.../rss"), ("Odia", "https://.../rss"), ("Urdu", "https://.../rss"),
]

RSS_SEARCH = "https://news.google.com/rss/search?q="

# translation (SIMPLE build: "builtin" needs NOTHING installed - it calls the free
# Google endpoint directly with Python's standard library. Use "none" to switch off.)
TRANSLATE_BACKEND = "builtin"         # "builtin" | "none"
MAX_TRANSLATE_PER_RUN = 4000
# natural-calamity exclusion
STRICT_NATURAL_EXCLUSION = True
INDIA_ONLY = True                     # drop accidents occurring outside India       # True: drop ANY item mentioning a calamity
# images
ENRICH = True
MAX_ENRICH_PER_RUN = 80
ENRICH_TIMEOUT = 12
# dedup
TITLE_DUP_THRESHOLD = 0.92
EVENT_SIM_THRESHOLD = 0.75
EVENT_DATE_WINDOW_DAYS = 2

DB_PATH = "accidents.db"
UA = "Mozilla/5.0 (compatible; AccidentMonitor/4.0)"

# ===========================================================================
# TRANSLATION
# ===========================================================================
_MOCK_TRANSLATE = None  # test hook: callable(text)->str


def translate_to_en(text):
    """SIMPLE build: translate via Google's free public endpoint using only the
    standard library (no pip install). Unofficial, so it can rate-limit; on any
    failure we return "" and the caller falls back to the digit/keyword method."""
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
    except Exception:
        return ""


# ===========================================================================
# DIGITS + CASUALTY EXTRACTION (works without translation)
# ===========================================================================
def _digit_map():
    m = {}
    for s in [0x0966, 0x09E6, 0x0A66, 0x0AE6, 0x0B66, 0x0BE6, 0x0C66, 0x0CE6, 0x0D66]:
        for d in range(10):
            m[chr(s + d)] = str(d)
    return str.maketrans(m)

DIGIT_TRANS = _digit_map()

DEATH_CUES = ["killed", "dead", "death", "died", "die ", "deceased", "toll", "lives lost", "perished",
              "मौत", "मृत", "मरे", "मृत्यु", "निधन", "ठार", "নিহত", "মৃত", "মৃত্যু",
              "இறந்த", "உயிரிழ", "பலி", "మృతి", "మృత్యు", "మరణ", "చనిపో", "ಸಾವು", "ಮೃತ", "ಬಲಿ",
              "മരണം", "മരിച്ച", "കൊല്ല", "મોત", "મૃત્યુ", "મૃત", "ਮੌਤ", "ਮਰੇ"]
INJURED_CUES = ["injured", "hurt", "wounded", "injuries", "घायल", "जख्मी", "আহত", "জখম", "जखमी",
                "காயம்", "படுகாயம்", "గాయ", "క్షతగా", "ಗಾಯ", "പരിക്ക", "ઘાયલ", "ઈજા",
                "ਜ਼ਖ਼ਮੀ", "ਜ਼ਖਮੀ", "ਘਾਇਲ"]


def extract_counts(text):
    t = text.translate(DIGIT_TRANS).lower()

    def near(cues, window=22):
        best = None
        for cue in cues:
            start = 0
            while True:
                i = t.find(cue.lower(), start)
                if i == -1:
                    break
                seg = t[max(0, i - window): i + len(cue) + window]
                base = max(0, i - window)
                for m in re.finditer(r"\d{1,4}", seg):
                    val = int(m.group())
                    if val > 500:
                        continue
                    dist = abs((m.start() + base) - i)
                    if best is None or dist < best[0]:
                        best = (dist, val)
                start = i + len(cue)
        return best[1] if best else None

    return near(DEATH_CUES), near(INJURED_CUES)


# ===========================================================================
# CATEGORY + NATURAL-CALAMITY CUES  (ordered: most specific first)
# ===========================================================================
CATEGORY_CUES = OrderedDict([
    ("pedestrian", ["pedestrian", "pedestrians", "run over", "ran over", "mowed down", "knocked down",
                    "hit while crossing", "पैदल", "राहगीर", "পথচারী", "பாதசாரி", "పాదచారి",
                    "ಪಾದಚಾರಿ", "കാൽനട", "રાહદારી", "ਪੈਦਲ"]),
    ("flight", ["plane", "planes", "aircraft", "aeroplane", "airplane", "helicopter", "chopper",
                "air crash", "aviation", "flight", "flights", "emergency landing", "crash landing",
                "runway", "विमान", "हेलिकॉप्टर", "বিমান", "হেলিকপ্টার", "விமான",
                "విమానం", "ವಿಮಾನ", "വിമാനം", "વિમાન", "ਜਹਾਜ਼"]),
    ("train", ["train", "trains", "railway", "rail", "derail*", "locomotive", "level crossing",
               "ट्रेन", "रेल", "রেল", "ট্রেন", "ரயில்", "రైలు", "ರೈಲು", "ട്രെയിൻ", "ટ્રેન", "ਰੇਲ"]),
    ("bus", ["bus", "buses", "minibus", "school bus", "बस", "বাস", "பேருந்து", "బస్సు", "ಬಸ್", "ബസ്", "બસ", "ਬੱਸ"]),
    ("cargo", ["truck", "trucks", "lorry", "lorries", "tanker", "tankers", "trailer", "goods vehicle", "container", "cargo",
               "dumper", "freight", "ट्रक", "लॉरी", "टैंकर", "ট্রাক", "லாரி", "ట్రక్", "ಟ್ರಕ್",
               "ലോറി", "ટ્રક", "ਟਰੱਕ"]),
    ("construction_infra", ["collaps*", "under construction", "under-construction", "scaffolding",
                            "girder", "construction site", "caved in", "building razed",
                            "under-construction building", "slab fell", "wall gave way",
                            "इमारत", "ढह", "दीवार", "भवन", "पुल", "फ्लाईओवर", "निर्माणाधीन", "কোসল",
                            "ভবন", "সেতু", "ধস", "निर्माण", "कोसळ", "पूल", "கட்டிடம்", "இடிந்து", "பாலம்",
                            "భవనం", "కూలి", "వంతెన", "ಕಟ್ಟಡ", "ಕುಸಿ", "ಸೇತುವೆ", "കെട്ടിടം", "തകർന്നു",
                            "പാലം", "ઇમారત", "ધરાશાયી", "પુલ", "ਇਮਾਰਤ", "ਢਹਿ", "ਪੁਲ"]),
    ("industrial", ["factory", "boiler", "gas leak", "industrial", "chemical plant", "refinery",
                    "mine collaps*", "mining", "फैक्ट्री", "कारखाना", "गैस रिसाव", "बॉयलर", "কারখানা",
                    "গ্যাস", "தொழிற்சாலை", "ఫ్యాక్టరీ", "ಕಾರ್ಖಾನೆ", "ഫാക്ടറി", "ફેક્ટરી", "ਫੈਕਟਰੀ", "खदान"]),
    ("traffic", ["road accident", "road mishap", "road crash", "car crash", "two-wheeler",
                 "motorcycle", "motorbike", "bike", "bikes", "scooter", "scooty", "suv", "van", "vans",
                 "auto-rickshaw", "autorickshaw", "jeep", "highway", "expressway", "सड़क", "हादसा",
                 "हाईवे", "राजमार्ग", "রাস্তা", "সড়ক", "पथ", "रस्ता", "சாலை", "நெடுஞ்சாலை", "రోడ్డు",
                 "హైవే", "ರಸ್ತೆ", "ಹೆದ್ದಾರಿ", "റോഡ്", "માર્ગ", "હાઈવે", "ਸੜਕ", "ਹਾਈਵੇ"]),
])

NATURAL_CUES = ["flood*", "deluge", "inundat*", "landslide", "landslip", "mudslide",
                "cloudburst", "avalanche", "earthquake", "quake", "tremor", "cyclone", "hurricane",
                "typhoon", "tornado", "tsunami", "lightning", "thunderbolt", "hailstorm", "wildfire",
                "forest fire", "storm surge", "glacier burst", "glacial lake",
                "बाढ़", "भूस्खलन", "भूकंप", "चक्रवात", "बिजली गिरने", "बादल फटने", "हिमस्खलन",
                "বন্যা", "ভূমিধস", "ভূমিকম্প", "ঘূর্ণিঝড়", "বজ্রপাত", "வெள்ளம்", "நிலச்சரிவு", "நிலநடுக்கம்",
                "మిన்னல்", "వరద", "కొండచరియ", "భూకంపం", "పిడుగు", "ಪ್ರವಾಹ", "ಭೂಕುಸಿತ", "ಭೂಕಂಪ", "ಸಿಡಿಲು",
                "വെള്ളപ്പൊക്കം", "ഉരുൾപൊട്ടൽ", "ഭൂകമ്പം", "પૂર", "ભૂસ્ખલન", "ધરતીકંપ", "ਹੜ੍ਹ", "ਭੂਚਾਲ"]


def _compile(cues):
    """ASCII cues -> word-boundary regex. A trailing '*' means 'any word suffix'
    (e.g. 'collaps*' matches collapse/collapses/collapsed). Non-ASCII cues are
    matched as plain substrings (Indic scripts have no simple word boundary)."""
    out = []
    for c in cues:
        c = c.strip()
        if not c.isascii():
            out.append(("sub", c))
        elif c.endswith("*"):
            out.append(("re", re.compile(r"\b" + re.escape(c[:-1]) + r"\w*", re.I)))
        else:
            out.append(("re", re.compile(r"\b" + re.escape(c) + r"\b", re.I)))
    return out

CATEGORY_PATTERNS = OrderedDict((cat, _compile(cues)) for cat, cues in CATEGORY_CUES.items())
NATURAL_PATTERNS = _compile(NATURAL_CUES)


def _hit(patterns, text, low):
    for kind, p in patterns:
        if kind == "re":
            if p.search(text):
                return True
        elif p in low:
            return True
    return False


def detect_category(text):
    low = text.lower()
    for cat, patterns in CATEGORY_PATTERNS.items():
        if _hit(patterns, text, low):
            return cat
    return None


def is_natural(text):
    return _hit(NATURAL_PATTERNS, text, text.lower())



# ===========================================================================
# GEOGRAPHIC FILTER - keep INDIA only
# Google News language editions leak across borders: the Bengali edition
# carries Bangladeshi outlets, and some foreign sites publish in Hindi.
# Field testing found ~24% of Bengali items came from Bangladeshi outlets.
# ===========================================================================
FOREIGN_SOURCES = [
 # Bangladesh
 "daily star","prothom alo","প্রথম আলো","ডেইলি স্টার","bss","bangladesh sangbad","unb",
 "bdnews24","kalerkantho","jugantor","ittefaq","samakal","bangla tribune","ajkalerkhobor",
 "banglanews","risingbd","bd-pratidin","dhaka post","dhakapost","dhaka mail","dhaka tribune",
 "naya diganta","নয়া দিগন্ত","ajker patrika","আজকের পত্রিকা","desh rupantor","দেশ রূপান্তর",
 "jagonews","somoy","channel24","jamuna","ntv bd","rtv","bangladesh pratidin","manabzamin",
 "amader shomoy","bhorer kagoj","observerbd","newagebd","tbsnews","businesspostbd",
 # Pakistan
 "dawn","geo news","ary news","express tribune","the news international","samaa","dunya",
 "jang","nawaiwaqt","bol news",
 # Nepal / Sri Lanka / others in South Asia
 "kathmandu post","himalayan times","onlinekhabar","ekantipur","setopati","myrepublica",
 "ada derana","colombo","daily mirror sri","newsfirst.lk","sundaytimes.lk",
 # Vietnam / East Asia sites that publish Indian-language pages
 "vietnam.vn","vnexpress","xinhua","global times","china daily",
 # International wires / broadcasters (their India-datelined copy is usually
 # duplicated by Indian outlets anyway)
 "bbc","al jazeera","cnn","sputnik","voa","dw.com","deutsche welle",
]

FOREIGN_PLACES = [
 # countries / regions, English
 "bangladesh","pakistan","nepal","sri lanka","afghanistan","myanmar","bhutan","maldives",
 "china","vietnam","hungary","thailand","indonesia","malaysia","singapore","philippines",
 "japan","korea","russia","ukraine","turkey","iran","iraq","syria","israel","egypt",
 "saudi arabia","dubai","abu dhabi","qatar","kuwait","oman","bahrain","yemen",
 "nigeria","kenya","ethiopia","congo","ghana","tanzania","uganda","south africa","morocco",
 "brazil","mexico","peru","bolivia","colombia","argentina","chile","venezuela","ecuador",
 "united states","u.s.","usa","america","canada","mexico city","texas","california",
 "florida","new york","chicago","washington","united kingdom","britain","england","london",
 "scotland","ireland","france","paris","germany","berlin","italy","rome","spain","madrid",
 "portugal","poland","greece","serbia","croatia","austria","switzerland","netherlands",
 "belgium","sweden","norway","denmark","finland","australia","new zealand","kazakhstan",
 "uzbekistan","azerbaijan","georgia","armenia","cambodia","laos","taiwan","hong kong",
 # Bangladeshi districts/cities that appear without the country name
 "dhaka","chattogram","chittagong","sylhet","khulna","rajshahi","barisal","rangpur","mymensingh",
 "feni","comilla","cumilla","narayanganj","gazipur","bogura","jessore","jashore","cox's bazar",
 "tangail","noakhali","brahmanbaria","dinajpur","pabna","kushtia","faridpur","madaripur",
 "gopalganj bd","munshiganj","manikganj","sirajganj","naogaon","natore","joypurhat",
 # native-script country names commonly seen
 "বাংলাদেশ","ঢাকা","চট্টগ্রাম","সিলেট","খুলনা","রাজশাহী","বরিশাল","রংপুর","ময়মনসিংহ",
 "হাঙ্গেরি","ভিয়েতনাম","পাকিস্তান","নেপাল","শ্রীলঙ্কা","সৌদি","চীন","ব্রাজিল","পোল্যান্ড",
 "बांग्लादेश","ढाका","पाकिस्तान","नेपाल","श्रीलंका","हंगरी","वियतनाम","चीन","सऊदी","ब्राजील",
 "म्यूनिख","रूस","यूक्रेन","अमेरिका","ब्रिटेन","लंदन",
 "பாகிஸ்தான்","வங்காளதேசம்","இலங்கை","சீனா","அமெரிக்கா",
 "పాకిస్తాన్","బంగ్లాదేశ్","శ్రీలంక","చైనా","అమెరికా",
 "ಪಾಕಿಸ್ತಾನ","ಬಾಂಗ್ಲಾದೇಶ","ಶ್ರೀಲಂಕಾ","ಚೀನಾ","ಅಮೆರಿಕ",
 "പാകിസ്ഥാൻ","ബംഗ്ലാദേശ്","ശ്രീലങ്ക","ചൈന","അമേരിക്ക",
 "પાકિસ્તાન","બાંગ્લાદેશ","શ્રીલંકા","ચીન","અમેરિકા",
 "ਪਾਕਿਸਤਾਨ","ਬੰਗਲਾਦੇਸ਼","ਸ਼੍ਰੀਲੰਕਾ","ਚੀਨ","ਅਮਰੀਕਾ",
]
FOREIGN_PLACE_PATTERNS = _compile(FOREIGN_PLACES)


def is_foreign(text, source=""):
    """True if the item looks like it is about another country."""
    s = (source or "").lower()
    for f in FOREIGN_SOURCES:
        if f in s:
            return True
    return _hit(FOREIGN_PLACE_PATTERNS, text, text.lower())


def classify(combined, source=""):
    """Return an in-scope category, or None if it should be dropped."""
    if INDIA_ONLY and is_foreign(combined, source):
        return None                      # accident in another country
    cat = detect_category(combined)
    if cat is None:
        return None
    if is_natural(combined) and STRICT_NATURAL_EXCLUSION:
        return None
    return cat


# ===========================================================================
# REPORTED CAUSE (preliminary / as-reported, NOT investigated root cause)
# Runs on the English (translated) + native text, so it works across sources
# and languages. Many items will have NO detectable cause -> left blank.
# ===========================================================================
CAUSE_CUES = OrderedDict([
    ("overspeeding", ["overspeed*", "speeding", "rash driving", "high speed", "reckless driving",
                      "तेज रफ्तार", "तेज़ रफ्तार", "तेज गति", "रैश ड्राइविंग"]),
    ("drunk_driving", ["drunk driving", "drink and drive", "drunken", "inebriated",
                       "under the influence", "नशे में", "शराब पीकर", "शराब के नशे"]),
    ("wrong_side_driving", ["wrong side", "wrong-side", "wrong lane", "wrong direction",
                            "विपरीत दिशा", "गलत दिशा"]),
    ("overtaking", ["overtaking", "overtake", "ओवरटेक"]),
    ("tyre_burst", ["tyre burst", "tire burst", "tyre blowout", "tire blowout",
                    "टायर फट", "टायर ब्लास्ट", "टायर फटने"]),
    ("brake_failure", ["brake failure", "brakes failed", "brake fail*", "brakes fail*", "ब्रेक फेल"]),
    ("overloading", ["overloaded", "overloading", "overcapacity", "क्षमता से अधिक", "ओवरलोड", "अधिक सवारी"]),
    ("driver_fatigue", ["fell asleep", "dozed off", "driver asleep", "fatigue", "drowsy",
                        "नींद", "झपकी", "सो गया"]),
    ("fog_poor_visibility", ["dense fog", "fog", "poor visibility", "low visibility", "smog", "mist",
                             "कोहरा", "धुंध", "कम दृश्यता"]),
    ("slippery_wet_road", ["wet road", "slippery road", "slippery", "गीली सड़क", "फिसलन"]),
    ("pothole_bad_road", ["pothole*", "bad road", "crater*", "damaged road", "गड्ढा", "गड्ढे",
                          "खराब सड़क", "जर्जर सड़क"]),
    ("signal_jump", ["jumped signal", "jumped the signal", "red light", "signal jump*",
                     "सिग्नल तोड़", "रेड लाइट"]),
    ("lost_control", ["lost control", "lost balance", "skid*", "veered", "swerved",
                      "नियंत्रण खो", "अनियंत्रित", "बेकाबू"]),
    ("head_on_collision", ["head-on", "head on collision", "collided head", "आमने-सामने", "आमने सामने"]),
    ("unmanned_crossing", ["unmanned crossing", "unmanned level crossing", "unmanned railway",
                           "मानवरहित क्रॉसिंग", "मानवरहित फाटक"]),
    ("trench_excavation_collapse", ["trench collaps*", "trench caved", "excavation collaps*",
                                    "pit collaps*", "खाई", "खुदाई", "गड्ढा धंस"]),
    ("structural_failure", ["structural failure", "gave way", "caved in", "substandard construction",
                            "poor construction", "dilapidated", "weak structure", "जर्जर", "भरभरा", "धंस", "ढह"]),
    ("scaffolding_failure", ["scaffolding collaps*", "scaffold fell", "scaffold gave way", "मचान"]),
    ("crane_failure", ["crane collaps*", "crane fell", "crane failure", "क्रेन गिर"]),
    ("wall_slab_roof_collapse", ["wall collaps*", "slab collaps*", "roof collaps*", "boundary wall",
                                 "दीवार गिर", "छत गिर", "स्लैब गिर"]),
    ("under_construction", ["under construction", "under-construction", "during construction",
                            "construction site", "निर्माणाधीन", "निर्माण कार्य"]),
    ("gas_leak", ["gas leak*", "toxic gas", "gas leakage", "ammonia leak", "chlorine leak",
                  "गैस रिसाव", "गैस लीक", "जहरीली गैस"]),
    ("boiler_blast", ["boiler blast", "boiler burst", "boiler explos*", "बॉयलर फट", "बॉयलर ब्लास्ट"]),
    ("explosion_blast", ["explosion", "cylinder blast", "gas cylinder", "विस्फोट", "धमाका", "सिलेंडर फट"]),
    ("fire_short_circuit", ["short circuit", "caught fire", "fire broke out", "massive fire",
                            "आग लग", "आगजनी", "शॉर्ट सर्किट", "शॉर्ट-सर्किट"]),
    ("electrocution", ["electrocuted", "electrocution", "live wire", "करंट", "बिजली का झटका", "करंट लग"]),
    ("suffocation_toxic_fumes", ["asphyxiation", "suffocation", "toxic fumes", "poisonous fumes",
                                 "दम घुट", "जहरीला धुआं"]),
    ("fell_into_water", ["fell into river", "fell into canal", "plunged into", "submerged", "drowned",
                         "पानी में गिर", "नदी में गिर", "डूब"]),
    ("fell_from_height", ["fell from height", "fell from building", "fell to death",
                          "ऊंचाई से गिर"]),
    ("hit_and_run", ["hit and run", "hit-and-run", "fled the spot", "fled after", "टक्कर मारकर फरार",
                     "मारकर फरार"]),
    ("rear_end_collision", ["rammed from behind", "rear-ended", "rear ended", "hit from behind",
                            "पीछे से टक्कर"]),
    ("hit_stationary_vehicle", ["parked truck", "stationary truck", "parked vehicle",
                                "stationary vehicle", "rammed into parked", "खड़े ट्रक", "खड़ी ट्रक"]),
    ("hit_divider_barrier", ["divider", "median", "crash barrier", "guardrail", "railing",
                             "डिवाइडर", "रेलिंग"]),
    ("animal_on_road", ["stray cattle", "cattle on", "stray animal", "nilgai", "stray dog",
                        "आवारा पशु", "मवेशी", "नीलगाय"]),
    ("hit_tree_pole", ["rammed into tree", "hit a tree", "crashed into tree", "electric pole",
                       "hit a pole", "पेड़ से टकरा", "खंभे से टकरा", "पेड़ से जा टकरा"]),
    ("gorge_valley_plunge", ["fell into gorge", "plunged into gorge", "plunges into gorge", "into a gorge", "into gorge", "fell into ravine",
                             "rolled down", "fell into valley", "deep gorge", "खाई में गिर",
                             "खड्ड में", "घाटी में गिर"]),
    ("borewell_fall", ["borewell", "bore well", "बोरवेल"]),
    ("manhole_drain", ["manhole", "open drain", "open nala", "storm drain", "मैनहोल",
                       "नाले में गिर", "नाले में बह"]),
    ("septic_sewer_deaths", ["septic tank", "sewer", "sewer line", "manual scavenging",
                             "सेप्टिक टैंक", "सीवर"]),
    ("lift_elevator", ["lift collapse", "lift crash", "elevator", "lift fell", "लिफ्ट"]),
    ("machinery_entrapment", ["caught in machine", "crushed by machine", "conveyor", "grinder",
                              "lathe", "मशीन में फंस", "मशीन में आ"]),
    ("load_beam_fall", ["load fell", "beam fell", "iron rod fell", "girder fell", "slab fell on",
                        "गर्डर गिर", "सरिया गिर"]),
    ("quarry_crusher_blast", ["quarry", "stone crusher", "stone quarry", "खदान में विस्फोट",
                              "क्रशर"]),
    ("chemical_spill_reaction", ["chemical reaction", "acid leak", "chemical spill", "toxic chemical",
                                 "रासायनिक", "एसिड"]),
    ("firecracker_unit", ["firecracker", "cracker unit", "cracker factory", "पटाखा"]),
    ("rail_signal_track_fault", ["signal failure", "track defect", "rail fracture", "points failure",
                                 "broken rail", "सिग्नल फेल", "पटरी टूट"]),
    ("crossing_railway_track", ["while crossing the track", "crossing railway track",
                                "crossing the tracks", "पटरी पार करते"]),
    ("fell_from_train", ["fell from train", "fell off train", "fell from moving train",
                         "चलती ट्रेन से गिर"]),
    ("overcrowding_footboard", ["footboard", "overcrowded", "overcrowding", "भीड़भाड़",
                                "फुटबोर्ड"]),
    ("mobile_distraction", ["using mobile", "on phone while", "talking on phone", "mobile phone while",
                            "मोबाइल पर बात"]),
    ("underage_driving", ["minor driving", "underage driving", "minor behind the wheel",
                          "नाबालिग चला"]),
    ("steering_axle_failure", ["steering failed", "steering failure", "axle broke", "axle breakage",
                               "स्टीयरिंग फेल", "एक्सल टूट"]),
    ("technical_snag_aviation", ["technical snag", "engine failure", "engine fire", "bird hit",
                                 "hydraulic failure", "तकनीकी खराबी"]),
    ("runway_excursion", ["overshot runway", "overshot the runway", "skidded off runway",
                          "veered off runway", "रनवे से फिसल"]),
    ("illegal_construction", ["illegal construction", "unauthorised construction",
                              "unauthorized construction", "illegal building", "अवैध निर्माण",
                              "अवैध इमारत"]),
    ("welding_spark", ["welding", "वेल्डिंग"]),
    ("speed_breaker", ["speed breaker", "स्पीड ब्रेकर"]),
    ("u_turn", ["taking u-turn", "u-turn", "यू-टर्न", "यू टर्न"]),
    ("triple_riding", ["triple riding", "riding triple", "तीन सवारी"]),
])
CAUSE_PATTERNS = OrderedDict((c, _compile(cues)) for c, cues in CAUSE_CUES.items())


def extract_causes(text, limit=6):
    """Return up to `limit` reported-cause labels found in the text, '; '-joined.
    Empty string means no cause was stated in the headline/snippet."""
    low = text.lower()
    found = []
    for cause, patterns in CAUSE_PATTERNS.items():
        if _hit(patterns, text, low):
            found.append(cause)
            if len(found) >= limit:
                break
    return "; ".join(found)


# ===========================================================================
# CITIES + HIGHWAYS
# ===========================================================================
CITIES = ["Mumbai", "Delhi", "New Delhi", "Kolkata", "Chennai", "Bengaluru", "Bangalore", "Hyderabad",
    "Ahmedabad", "Pune", "Jaipur", "Lucknow", "Kanpur", "Nagpur", "Patna", "Bhopal", "Indore", "Thane",
    "Visakhapatnam", "Vadodara", "Ghaziabad", "Ludhiana", "Agra", "Nashik", "Faridabad", "Meerut",
    "Rajkot", "Varanasi", "Srinagar", "Aurangabad", "Dhanbad", "Amritsar", "Prayagraj", "Allahabad",
    "Ranchi", "Howrah", "Coimbatore", "Jabalpur", "Gwalior", "Vijayawada", "Jodhpur", "Madurai",
    "Raipur", "Kota", "Guwahati", "Chandigarh", "Thiruvananthapuram", "Solapur", "Hubballi", "Bareilly",
    "Mysuru", "Mysore", "Gurugram", "Gurgaon", "Noida", "Aligarh", "Jalandhar", "Bhubaneswar", "Salem",
    "Warangal", "Guntur", "Saharanpur", "Gorakhpur", "Bikaner", "Amravati", "Jamshedpur", "Bhilai",
    "Cuttack", "Kochi", "Nellore", "Bhavnagar", "Dehradun", "Durgapur", "Asansol", "Rourkela", "Nanded",
    "Kolhapur", "Ajmer", "Kalaburagi", "Jamnagar", "Ujjain", "Siliguri", "Jhansi", "Mangaluru",
    "Mangalore", "Erode", "Belagavi", "Tirupati", "Udaipur", "Panaji", "Shillong", "Imphal", "Aizawl",
    "Kohima", "Itanagar", "Gangtok", "Agartala", "Shimla", "Puducherry", "Vellore", "Tiruchirappalli",
    "Trichy", "Tirunelveli", "Tiruppur", "Kozhikode", "Thrissur", "Kollam", "Kannur", "Muzaffarpur",
    "Gaya", "Bhagalpur", "Darbhanga", "Rohtak", "Panipat", "Karnal", "Ambala", "Hisar", "Sonipat",
    "Moradabad", "Junagadh", "Anand", "Surat", "Navi Mumbai", "Kalyan", "Sangli", "Latur", "Akola",
    "Ratlam", "Sagar", "Satna", "Rewa", "Bilaspur", "Korba", "Sambalpur", "Berhampur", "Puri",
    "Dibrugarh", "Silchar", "Tezpur", "Jorhat", "Nagaon"]

# --- Additional district/town names (extracted locations were missing on ~90%
# --- of items in field testing, so the gazetteer was widened considerably).
CITIES += ["Ambattur","Avadi","Tambaram","Thoothukudi","Dindigul","Thanjavur","Nagercoil",
 "Karur","Cuddalore","Kancheepuram","Vellore","Namakkal","Sivakasi","Virudhunagar","Karaikudi",
 "Palakkad","Alappuzha","Kottayam","Malappuram","Pathanamthitta","Idukki","Wayanad","Kasaragod",
 "Ernakulam","Munnar","Guruvayur","Ballari","Davanagere","Shivamogga","Tumakuru","Raichur",
 "Bidar","Hassan","Udupi","Chikkamagaluru","Chitradurga","Bagalkot","Vijayapura","Karwar",
 "Kurnool","Kadapa","Anantapur","Rajahmundry","Kakinada","Eluru","Ongole","Srikakulam",
 "Vizianagaram","Machilipatnam","Chittoor","Karimnagar","Khammam","Nizamabad","Ramagundam",
 "Mahbubnagar","Adilabad","Siddipet","Sangareddy","Medak","Nalgonda",
 "Ahmednagar","Jalgaon","Chandrapur","Parbhani","Beed","Osmanabad","Wardha","Yavatmal",
 "Bhusawal","Panvel","Vasai","Virar","Mira Road","Dombivli","Ulhasnagar","Ichalkaranji",
 "Satara","Ratnagiri","Sindhudurg","Raigad","Palghar","Nandurbar","Dhule","Buldhana",
 "Gondia","Bhandara","Washim","Hingoli","Jalna",
 "Bhiwandi","Malegaon","Baramati","Karad","Sangamner",
 "Muzaffarnagar","Shamli","Baghpat","Hapur","Bulandshahr","Amroha","Sambhal","Rampur",
 "Bijnor","Pilibhit","Shahjahanpur","Hardoi","Sitapur","Lakhimpur","Barabanki","Unnao",
 "Raebareli","Fatehpur","Banda","Hamirpur","Mahoba","Jalaun","Etawah","Auraiya","Kannauj",
 "Farrukhabad","Mainpuri","Firozabad","Mathura","Hathras","Kasganj","Etah","Budaun",
 "Ayodhya","Faizabad","Sultanpur","Amethi","Pratapgarh","Jaunpur","Ghazipur","Ballia",
 "Mau","Azamgarh","Deoria","Kushinagar","Maharajganj","Basti","Gonda","Bahraich",
 "Shravasti","Balrampur","Siddharthnagar","Mirzapur","Sonbhadra","Chandauli","Bhadohi",
 "Rohtas","Sasaram","Arrah","Buxar","Chhapra","Siwan","Gopalganj","Bettiah","Motihari",
 "Sitamarhi","Madhubani","Samastipur","Begusarai","Khagaria","Munger","Jamui","Nawada",
 "Nalanda","Bihar Sharif","Aurangabad Bihar","Jehanabad","Katihar","Purnia","Araria",
 "Kishanganj","Supaul","Saharsa","Madhepura",
 "Bokaro","Deoghar","Hazaribagh","Giridih","Ramgarh","Chaibasa","Dumka","Palamu","Daltonganj",
 "Bardhaman","Malda","Krishnanagar","Barasat","Baharampur","Jalpaiguri","Cooch Behar",
 "Alipurduar","Raiganj","Balurghat","Bankura","Purulia","Midnapore","Kharagpur","Haldia",
 "Diamond Harbour","Barrackpore","Serampore","Chandannagar","Habra","Bongaon","Basirhat",
 "Bhilwara","Alwar","Sikar","Pali","Barmer","Jaisalmer","Nagaur","Churu","Jhunjhunu",
 "Hanumangarh","Sri Ganganagar","Bharatpur","Dholpur","Karauli","Sawai Madhopur","Bundi",
 "Baran","Jhalawar","Chittorgarh","Banswara","Dungarpur","Sirohi","Jalore","Rajsamand",
 "Morena","Bhind","Shivpuri","Guna","Vidisha","Sehore","Raisen","Hoshangabad","Betul",
 "Chhindwara","Seoni","Balaghat","Mandla","Dindori","Shahdol","Umaria","Katni","Damoh",
 "Panna","Chhatarpur","Tikamgarh","Datia","Ashoknagar","Neemuch","Mandsaur","Dewas",
 "Shajapur","Khandwa","Khargone","Barwani","Dhar","Jhabua","Ratlam MP",
 "Durg","Rajnandgaon","Jagdalpur","Ambikapur","Raigarh","Janjgir","Mahasamund","Dhamtari",
 "Kanker","Dantewada","Sukma","Bijapur Chhattisgarh",
 "Balasore","Bhadrak","Jajpur","Kendrapara","Jagatsinghpur","Angul","Dhenkanal","Keonjhar",
 "Mayurbhanj","Baripada","Sundargarh","Jharsuguda","Bargarh","Bolangir","Kalahandi",
 "Koraput","Rayagada","Nabarangpur","Malkangiri","Nuapada","Boudh","Ganjam","Gajapati",
 "Anantnag","Baramulla","Udhampur","Kathua","Rajouri","Poonch","Doda","Kishtwar","Leh",
 "Kargil","Jammu",
 "Solan","Mandi","Kullu","Kangra","Dharamshala","Una","Hamirpur HP","Bilaspur HP","Chamba",
 "Kinnaur","Lahaul","Sirmaur","Nahan","Palampur",
 "Haridwar","Rishikesh","Roorkee","Haldwani","Rudrapur","Kashipur","Nainital","Almora",
 "Pithoragarh","Chamoli","Rudraprayag","Uttarkashi","Tehri","Pauri","Bageshwar","Champawat",
 "Bathinda","Patiala","Mohali","Pathankot","Hoshiarpur","Moga","Firozpur","Faridkot",
 "Muktsar","Barnala","Sangrur","Kapurthala","Gurdaspur","Batala","Khanna","Phagwara",
 "Rewari","Bhiwani","Jind","Kaithal","Kurukshetra","Yamunanagar","Sirsa","Fatehabad",
 "Palwal","Nuh","Mahendragarh","Charkhi Dadri","Jhajjar",
 "Bharuch","Ankleshwar","Vapi","Valsad","Navsari","Mehsana","Patan","Palanpur","Godhra",
 "Nadiad","Bhuj","Gandhidham","Morbi","Surendranagar","Amreli","Porbandar","Veraval",
 "Botad","Dahod","Gandhinagar",
 "Dibang","Tinsukia","Sivasagar","Golaghat","Bongaigaon","Barpeta","Dhubri","Goalpara",
 "Karimganj","Hailakandi","Diphu","Haflong","Lakhimpur Assam","Sonitpur",
 "Dimapur","Tura","Jowai","Churachandpur","Lunglei","Namchi","Pasighat","Tawang",
 "Rourkela Steel","Vasco","Margao","Mapusa","Ponda",
 "Karaikal","Mahe","Yanam","Port Blair","Kavaratti","Silvassa","Daman","Diu"]
CITIES += ["Uttar Pradesh","Madhya Pradesh","Maharashtra","Rajasthan","Tamil Nadu","Karnataka",
 "Kerala","Gujarat","Bihar","West Bengal","Odisha","Telangana","Andhra Pradesh","Punjab",
 "Haryana","Jharkhand","Chhattisgarh","Assam","Uttarakhand","Himachal Pradesh","Goa",
 "Tripura","Meghalaya","Manipur","Nagaland","Mizoram","Arunachal Pradesh","Sikkim",
 "Jammu and Kashmir","Ladakh","Delhi NCR"]

# Native-script names for the largest cities, so a report written only in an
# Indian script still yields a joinable location even if translation fails.
CITY_ALIASES = {
 "Delhi": ["दिल्ली","দিল্লি","டெல்லி","ఢిల్లీ","ದೆಹಲಿ","ഡൽഹി","દિલ્હી","ਦਿੱਲੀ"],
 "Mumbai": ["मुंबई","মুম্বই","மும்பை","ముంబై","ಮುಂಬೈ","മുംബൈ","મુંબઈ","ਮੁੰਬਈ"],
 "Kolkata": ["कोलकाता","কলকাতা","கொல்கத்தா","కోల్‌కతా","ಕೋಲ್ಕತ್ತಾ","കൊൽക്കത്ത","કોલકાતા"],
 "Chennai": ["चेन्नई","চেন্নাই","சென்னை","చెన్నై","ಚೆನ್ನೈ","ചെന്നൈ","ચેન્નઈ"],
 "Bengaluru": ["बेंगलुरु","বেঙ্গালুরু","பெங்களூரு","బెంగళూరు","ಬೆಂಗಳೂರು","ബെംഗളൂരു","બેંગલુરુ"],
 "Hyderabad": ["हैदराबाद","হায়দরাবাদ","ஹைதராபாத்","హైదరాబాద్","ಹೈದರಾಬಾದ್","ഹൈദരാബാദ്","હૈદરાબાદ"],
 "Pune": ["पुणे","পুনে","புனே","పూణే","ಪುಣೆ","പൂനെ","પુણે"],
 "Ahmedabad": ["अहमदाबाद","আহমেদাবাদ","அகமதாபாத்","అహ్మదాబాద్","ಅಹಮದಾಬಾದ್","અમદાવાદ"],
 "Jaipur": ["जयपुर","জয়পুর","ஜெய்ப்பூர்","జైపూర్","ಜೈಪುರ","ജയ്പുർ","જયપુર"],
 "Lucknow": ["लखनऊ","লখনউ","லக்னோ","లక్నో","ಲಕ್ನೋ","લખનૌ"],
 "Kanpur": ["कानपुर","কানপুর","கான்பூர்","కాన్పూర్","ಕಾನ್ಪುರ"],
 "Patna": ["पटना","পাটনা","பாட்னா","పాట్నా","ಪಟ್ನಾ","પટના"],
 "Nagpur": ["नागपुर","নাগপুর","நாக்பூர்","నాగ్‌పూర్","�ನಾಗ್ಪುರ"],
 "Bhopal": ["भोपाल","ভোপাল","போபால்","భోపాల్","ಭೋಪಾಲ್"],
 "Indore": ["इंदौर","ইন্দোর","இந்தூர்","ఇండోర్","ಇಂದೋರ್"],
 "Surat": ["सूरत","সুরাট","சூரத்","సూరత్","ಸೂರತ್","સુરત"],
 "Varanasi": ["वाराणसी","বারাণসী","வாரணாசி","వారణాసి","ವಾರಾಣಸಿ"],
 "Guwahati": ["गुवाहाटी","গুয়াহাটি","கவுகாத்தி","గువహాటి"],
 "Coimbatore": ["कोयंबटूर","கோயம்புத்தூர்","కోయంబత్తూరు","ಕೊಯಮತ್ತೂರು"],
 "Visakhapatnam": ["विशाखापत्तनम","বিশাখাপত্তনম","விசாகப்பட்டினம்","విశాఖపట్నం","ವಿಶಾಖಪಟ್ಟಣಂ"],
 "Thiruvananthapuram": ["तिरुवनंतपुरम","திருவனந்தபுரம்","తిరువనంతపురం","തിരുവനന്തപുരം"],
 "Kochi": ["कोच्चि","কোচি","கொச்சி","కొచ్చి","ಕೊಚ್ಚಿ","കൊച്ചി"],
 "Ludhiana": ["लुधियाना","লুধিয়ানা","ਲੁਧਿਆਣਾ","లూధియానా"],
 "Amritsar": ["अमृतसर","অমৃতসর","ਅੰਮ੍ਰਿਤਸਰ","அமிர்தசரஸ்"],
 "Gurugram": ["गुरुग्राम","গুরুগ্রাম","గురుగ్రామ్"],
 "Noida": ["नोएडा","নয়ডা","நொய்டா","నోయిడా"],
 "Ranchi": ["रांची","রাঁচি","ராஞ்சி","రాంచీ"],
 "Raipur": ["रायपुर","রায়পুর","ராய்பூர்","రాయ్‌పూర్"],
 "Bhubaneswar": ["भुवनेश्वर","ভুবনেশ্বর","புவனேஸ்வர்","భువనేశ్వర్"],
 "Dehradun": ["देहरादून","দেরাদুন","டேராடூன்","డెహ్రాడూన్"],
 "Srinagar": ["श्रीनगर","শ্রীনগর","ஸ்ரீநகர்","శ్రీనగర్"],
 "Madurai": ["मदुरै","মাদুরাই","மதுரை","మధురై","ಮಧುರೈ"],
 "Mysuru": ["मैसूर","মহীশূর","மைசூர்","మైసూరు","ಮೈಸೂರು"],
 "Vijayawada": ["विजयवाड़ा","বিজয়ওয়াড়া","விஜயவாடா","విజయవాడ","ವಿಜಯವಾಡ"],
 "Kozhikode": ["कोझिकोड","கோழிக்கோடு","കോഴിക്കോട്"],
 "Thrissur": ["त्रिशूर","திருச்சூர்","തൃശൂർ"],
 "Nashik": ["नाशिक","নাসিক","நாசிக்","నాసిక్"],
 "Tiruchirappalli": ["तिरुचिरापल्ली","திருச்சிராப்பள்ளி","తిరుచిరాపల్లి"],
}

CITIES = sorted(set(CITIES), key=len, reverse=True)
_CITY_PATTERNS = [(c, re.compile(r"\b" + re.escape(c) + r"\b", re.IGNORECASE)) for c in CITIES]
_HIGHWAY_PATTERNS = [
    re.compile(r"\bNH[-\s]?\d{1,3}[A-Z]?\b", re.IGNORECASE),
    re.compile(r"\bSH[-\s]?\d{1,3}[A-Z]?\b", re.IGNORECASE),
    re.compile(r"\bNational Highway[-\s]?\d{1,3}[A-Z]?\b", re.IGNORECASE),
    re.compile(r"\bState Highway[-\s]?\d{1,3}[A-Z]?\b", re.IGNORECASE),
    re.compile(r"\b[A-Z][a-z]+(?:[-\s][A-Z][a-z]+)?\s+Expressway\b"),
]


def extract_locations(text):
    if not text:
        return "", ""
    cities, seen = [], set()
    for name, pat in _CITY_PATTERNS:
        if pat.search(text) and name.lower() not in seen:
            cities.append(name); seen.add(name.lower())
    # native-script aliases map back to the canonical English name, so a Hindi
    # and an English report of the same city produce the SAME join key
    for canon, aliases in CITY_ALIASES.items():
        if canon.lower() in seen:
            continue
        for a in aliases:
            if a in text:
                cities.append(canon); seen.add(canon.lower())
                break
    highways, hseen = [], set()
    for pat in _HIGHWAY_PATTERNS:
        for m in pat.findall(text):
            h = re.sub(r"[-\s]+", "-", m.strip())
            if h.lower() not in hseen:
                highways.append(h); hseen.add(h.lower())
    return "; ".join(cities), "; ".join(highways)


def _set(s):
    return {x.strip().lower() for x in s.split(";") if x.strip()}


def _hwset(s):
    return {re.sub(r"[-\s]+", "-", x.strip().lower()) for x in s.split(";") if x.strip()}


# ===========================================================================
# DATABASE
# ===========================================================================
COLUMNS = OrderedDict([
    ("id", "TEXT PRIMARY KEY"), ("title", "TEXT"), ("title_en", "TEXT"), ("url", "TEXT"),
    ("resolved_url", "TEXT"), ("source", "TEXT"), ("published", "TEXT"), ("published_ts", "REAL"),
    ("category", "TEXT"), ("language", "TEXT"), ("query", "TEXT"), ("title_norm", "TEXT"),
    ("snippet", "TEXT"), ("image_url", "TEXT"), ("cities", "TEXT"), ("highways", "TEXT"),
    ("deaths", "INTEGER"), ("injured", "INTEGER"), ("cause", "TEXT"), ("fetched_at", "TEXT"),
    ("is_duplicate", "INTEGER DEFAULT 0"), ("dup_group", "TEXT"), ("translated", "INTEGER DEFAULT 0"),
])


def init_db(conn):
    conn.execute(f"CREATE TABLE IF NOT EXISTS articles ({', '.join(f'{k} {v}' for k,v in COLUMNS.items())})")
    existing = {r[1] for r in conn.execute("PRAGMA table_info(articles)")}
    for col, decl in COLUMNS.items():
        if col not in existing:
            conn.execute(f"ALTER TABLE articles ADD COLUMN {col} {decl.replace(' PRIMARY KEY','')}")
    conn.commit()


# ===========================================================================
# FETCH + PARSE
# ===========================================================================
def feed_url(query, code, ceid):
    return f"{RSS_SEARCH}{urllib.parse.quote(query)}&hl={code}-IN&gl=IN&ceid={ceid}"


def http_get(url, timeout=30, retries=3):
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    for attempt in range(retries):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read(), resp.geturl()
        except Exception:  # noqa: BLE001
            if attempt == retries - 1:
                return None, None
            time.sleep(2 * (attempt + 1))
    return None, None


def _strip_ns(tag):
    return tag.split("}", 1)[-1] if "}" in tag else tag


def feed_image_from_item(item, description):
    for el in item.iter():
        tag = _strip_ns(el.tag)
        if tag in ("content", "thumbnail") and el.get("url") and "image" in (el.get("type") or "image"):
            return el.get("url")
        if tag == "enclosure" and el.get("url") and "image" in (el.get("type") or ""):
            return el.get("url")
    m = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', description or "", re.I)
    return m.group(1) if m else ""


def looks_incident(text):
    return detect_category(text) is not None or is_natural(text) or extract_counts(text) != (None, None)


def parse_feed(xml_bytes, language, query, prefilter=False):
    out = []
    if not xml_bytes:
        return out
    try:
        root = ElementTree.fromstring(xml_bytes)
    except ElementTree.ParseError:
        return out
    for item in root.iter("item"):
        title = (item.findtext("title") or "").strip()
        if not title:
            continue
        description = item.findtext("description") or ""
        desc_text = re.sub(r"<[^>]+>", " ", description).strip()
        combined = title + " " + desc_text
        if prefilter and not looks_incident(combined):
            continue
        link = (item.findtext("link") or "").strip()
        pub_raw = (item.findtext("pubDate") or "").strip()
        src_el = item.find("source")
        source = src_el.text.strip() if src_el is not None and src_el.text else ""
        ts, iso = parse_date(pub_raw)
        out.append({
            "id": hashlib.sha1(normalize_title(title).encode("utf-8")).hexdigest(),
            "title": title, "url": link, "source": source, "published": iso, "published_ts": ts,
            "language": language, "query": query, "title_norm": normalize_title(title),
            "snippet": desc_text[:400], "image_url": feed_image_from_item(item, description),
            "fetched_at": datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S"),
        })
    return out


def parse_date(pub_raw):
    if pub_raw:
        try:
            dt = parsedate_to_datetime(pub_raw)
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt.timestamp(), dt.strftime("%Y-%m-%d")
        except (TypeError, ValueError):
            pass
    now = datetime.now(timezone.utc)
    return now.timestamp(), now.strftime("%Y-%m-%d")


def normalize_title(title):
    t = title.lower()
    t = re.sub(r"\s+-\s+[^-]+$", "", t)
    t = re.sub(r"[^\w\u0900-\u0d7f ]", " ", t, flags=re.UNICODE)
    return re.sub(r"\s+", " ", t).strip()


# ===========================================================================
# IMAGE ENRICHMENT
# ===========================================================================
_OG_IMG = re.compile(r'<meta[^>]+(?:property|name)=["\']og:image["\'][^>]+content=["\']([^"\']+)["\']', re.I)
_OG_IMG_R = re.compile(r'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\']og:image["\']', re.I)


def enrich_image(url):
    data, final = http_get(url, timeout=ENRICH_TIMEOUT, retries=1)
    if not data:
        return "", ""
    page = data.decode("utf-8", "ignore")
    m = _OG_IMG.search(page) or _OG_IMG_R.search(page)
    return (final or ""), (html.unescape(m.group(1)) if m else "")


# ===========================================================================
# DEDUP
# ===========================================================================
def event_similarity(a, b):
    parts, weights = [], []
    strong = False
    da, db = a["deaths"], b["deaths"]
    if da is not None and db is not None:
        parts.append(1.0 if da == db else (0.5 if abs(da - db) <= 1 else 0.0)); weights.append(0.40)
        strong = strong or da == db
    ia, ib = a["injured"], b["injured"]
    if ia is not None and ib is not None:
        parts.append(1.0 if ia == ib else (0.5 if abs(ia - ib) <= 2 else 0.0)); weights.append(0.20)
    ca, cb = _set(a["cities"]), _set(b["cities"])
    if ca and cb:
        parts.append(1.0 if ca & cb else 0.0); weights.append(0.30); strong = strong or bool(ca & cb)
    ha, hb = _hwset(a["highways"]), _hwset(b["highways"])
    if ha and hb:
        parts.append(1.0 if ha & hb else 0.0); weights.append(0.20); strong = strong or bool(ha & hb)
    if a["language"] == b["language"]:
        r = SequenceMatcher(None, a["title_norm"], b["title_norm"]).ratio()
        parts.append(r); weights.append(0.25); strong = strong or r >= TITLE_DUP_THRESHOLD
    if not parts:
        return 0.0, False
    return sum(p * w for p, w in zip(parts, weights)) / sum(weights), strong


def find_duplicate(conn, a):
    lo = a["published_ts"] - EVENT_DATE_WINDOW_DAYS * 86400
    hi = a["published_ts"] + EVENT_DATE_WINDOW_DAYS * 86400
    best = None
    for r in conn.execute(
        """SELECT id,dup_group,title_norm,language,cities,highways,deaths,injured
           FROM articles WHERE category=? AND published_ts BETWEEN ? AND ?""",
            (a["category"], lo, hi)):
        b = {"id": r[0], "dup_group": r[1], "title_norm": r[2], "language": r[3],
             "cities": r[4] or "", "highways": r[5] or "", "deaths": r[6], "injured": r[7]}
        score, strong = event_similarity(a, b)
        if score >= EVENT_SIM_THRESHOLD and strong and (best is None or score > best[1]):
            best = (b["dup_group"] or b["id"], score)
    return best[0] if best else None


# ===========================================================================
# STORE  (translate -> classify -> exclude natural -> enrich -> dedup -> insert)
# ===========================================================================
def store(conn, articles, enrich_budget, translate_budget):
    new = 0
    for a in articles:
        if conn.execute("SELECT 1 FROM articles WHERE id=?", (a["id"],)).fetchone():
            continue

        native = a["title"] + " " + a.get("snippet", "")
        title_en = ""
        translated = 0
        if a["language"] != "English" and TRANSLATE_BACKEND != "none" and translate_budget > 0:
            tx = translate_to_en((a["title"] + "\n" + a.get("snippet", ""))[:4900])
            translate_budget -= 1
            if tx:
                title_en = tx
                translated = 1

        english = title_en
        combined = (english + " " + native).strip()

        category = classify(combined, a.get('source', ''))
        if category is None:
            continue  # not in-scope, or a natural calamity -> dropped

        # image enrichment only for kept items
        resolved_url = ""
        if ENRICH and enrich_budget > 0 and not a.get("image_url"):
            resolved_url, img = enrich_image(a["url"])
            enrich_budget -= 1
            if img:
                a["image_url"] = img
            time.sleep(0.3)

        deaths, injured = extract_counts(native + " " + english)
        cities, highways = extract_locations(combined)
        cause = extract_causes(combined)
        a.update({"category": category, "deaths": deaths, "injured": injured,
                  "cities": cities, "highways": highways})

        canonical = find_duplicate(conn, a)
        is_dupe = 1 if canonical else 0
        dup_group = canonical or a["id"]

        conn.execute(
            """INSERT OR IGNORE INTO articles
               (id,title,title_en,url,resolved_url,source,published,published_ts,category,language,
                query,title_norm,snippet,image_url,cities,highways,deaths,injured,cause,fetched_at,
                is_duplicate,dup_group,translated)
               VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (a["id"], a["title"], title_en, a["url"], resolved_url, a["source"], a["published"],
             a["published_ts"], category, a["language"], a["query"], a["title_norm"],
             a.get("snippet", ""), a["image_url"], cities, highways, deaths, injured,
             cause, a["fetched_at"], is_dupe, dup_group, translated))
        new += 1
    conn.commit()
    return new, enrich_budget, translate_budget


# ===========================================================================
# EXPORTS
# ===========================================================================

def backfill_translations(conn, budget):
    """Rows saved on earlier runs WITHOUT a translation stay untranslated forever
    unless we revisit them. The free endpoint throttles (field testing translated
    ~550 items before being cut off), so each run picks up where the last stopped.
    Coverage therefore accumulates across days instead of stalling."""
    if TRANSLATE_BACKEND == "none" or budget <= 0:
        return 0
    rows = conn.execute(
        """SELECT id,title,snippet,language FROM articles
           WHERE (title_en IS NULL OR title_en='') AND language!='English'
           ORDER BY published_ts DESC LIMIT ?""", (budget,)).fetchall()
    done = 0
    for rid, title, snippet, lang in rows:
        tx = translate_to_en((title + "\n" + (snippet or ""))[:1800])
        if not tx:
            break                      # throttled - stop, resume next run
        combined = tx + " " + title + " " + (snippet or "")
        cities, highways = extract_locations(combined)
        deaths, injured = extract_counts(title + " " + (snippet or "") + " " + tx)
        cause = extract_causes(combined)
        conn.execute("""UPDATE articles SET title_en=?,translated=1,cities=?,highways=?,
                        deaths=COALESCE(deaths,?),injured=COALESCE(injured,?),
                        cause=CASE WHEN cause='' THEN ? ELSE cause END
                        WHERE id=?""",
                     (tx, cities, highways, deaths, injured, cause, rid))
        done += 1
        time.sleep(0.25)               # be gentle with the free service
    conn.commit()
    if done:
        print(f"[translate-backfill] filled {done} older items")
    return done


def rededupe(conn):
    """Re-run duplicate detection over the whole table. Needed because items get
    richer over time (translation adds city/casualty data), which reveals matches
    that were invisible when the item was first stored."""
    conn.execute("UPDATE articles SET is_duplicate=0, dup_group=id")
    rows = conn.execute(
        """SELECT id,title_norm,language,cities,highways,deaths,injured,category,published_ts
           FROM articles ORDER BY published_ts ASC""").fetchall()
    seen = []
    merged = 0
    for r in rows:
        a = {"id": r[0], "title_norm": r[1], "language": r[2], "cities": r[3] or "",
             "highways": r[4] or "", "deaths": r[5], "injured": r[6], "category": r[7],
             "published_ts": r[8] or 0}
        best = None
        for b in seen:
            if b["category"] != a["category"]:
                continue
            if abs((b["published_ts"] or 0) - a["published_ts"]) > EVENT_DATE_WINDOW_DAYS * 86400:
                continue
            score, strong = event_similarity(a, b)
            if score >= EVENT_SIM_THRESHOLD and strong and (best is None or score > best[1]):
                best = (b["dup_group"], score)
        if best:
            conn.execute("UPDATE articles SET is_duplicate=1, dup_group=? WHERE id=?", (best[0], a["id"]))
            a["dup_group"] = best[0]
            merged += 1
        else:
            a["dup_group"] = a["id"]
        seen.append(a)
        if len(seen) > 4000:
            seen = seen[-4000:]
    conn.commit()
    print(f"[re-dedup] {merged} duplicates across the whole database")
    return merged


def export_articles_csv(conn, path="articles.csv"):
    rows = conn.execute(
        """SELECT published,language,category,cause,source,title,title_en,cities,highways,
                  deaths,injured,image_url,url,is_duplicate,dup_group
           FROM articles ORDER BY published_ts DESC""").fetchall()
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["published", "language", "category", "cause", "source", "title", "title_en",
                    "cities", "highways", "deaths", "injured", "image_url", "url",
                    "is_duplicate", "dup_group"])
        w.writerows(rows)
    return len(rows)


def export_cause_summary_csv(conn, path="cause_summary.csv"):
    """Counts of reported causes per category (unique events only)."""
    counts = Counter()
    for cat, cause in conn.execute(
            "SELECT category, cause FROM articles WHERE is_duplicate=0"):
        if not cause:
            counts[(cat, "unstated")] += 1
            continue
        for part in cause.split(";"):
            part = part.strip()
            if part:
                counts[(cat, part)] += 1
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["category", "reported_cause", "unique_events"])
        for (cat, cause), n in sorted(counts.items(), key=lambda x: (x[0][0], -x[1])):
            w.writerow([cat, cause, n])


def export_cause_trend_csv(conn, path="cause_trend_monthly.csv"):
    """Month-by-month counts per reported cause (unique events only) - this is
    the file to chart for 'which causes are repeating / rising'."""
    counts = Counter()
    for month, cause in conn.execute(
            "SELECT strftime('%Y-%m', published), cause FROM articles WHERE is_duplicate=0"):
        if not cause:
            counts[(month, "unstated")] += 1
            continue
        for part in cause.split(";"):
            part = part.strip()
            if part:
                counts[(month, part)] += 1
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["month", "reported_cause", "unique_events"])
        for (month, cause), n in sorted(counts.items(), key=lambda x: (x[0][0], -x[1]), reverse=True):
            w.writerow([month, cause, n])


def _summary(conn, period):
    return conn.execute(
        f"""SELECT strftime('{period}',published) p, category, COUNT(*)
            FROM articles WHERE is_duplicate=0
            GROUP BY p, category ORDER BY p DESC, category""").fetchall()


def export_summary_csv(conn, period, path):
    rows = _summary(conn, period)
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["period", "category", "unique_events"])
        w.writerows(rows)


def top_counts(conn, column, limit=15):
    c = Counter()
    for (val,) in conn.execute(f"SELECT {column} FROM articles WHERE is_duplicate=0 AND {column}!=''"):
        for part in val.split(";"):
            if part.strip():
                c[part.strip()] += 1
    return c.most_common(limit)


def export_dashboard(conn, path="index.html"):
    monthly = _summary(conn, "%Y-%m")
    periods, cats = {}, set()
    for p, cat, n in monthly:
        periods.setdefault(p, {})[cat] = n
        cats.add(cat)
    cats = sorted(cats)
    total = conn.execute("SELECT COUNT(*) FROM articles WHERE is_duplicate=0").fetchone()[0]
    total_raw = conn.execute("SELECT COUNT(*) FROM articles").fetchone()[0]
    merged = total_raw - total
    with_img = conn.execute("SELECT COUNT(*) FROM articles WHERE image_url!=''").fetchone()[0]
    with_cause = conn.execute("SELECT COUNT(*) FROM articles WHERE is_duplicate=0 AND cause!=''").fetchone()[0]
    last = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    head = "".join(f"<th>{html.escape(c)}</th>" for c in cats)
    body = ""
    for p in sorted(periods, reverse=True):
        cells = "".join(f"<td>{periods[p].get(c,0)}</td>" for c in cats)
        body += f"<tr><th>{html.escape(p)}</th>{cells}<td class='tot'>{sum(periods[p].values())}</td></tr>"

    def rows_html(pairs):
        return "".join(f"<tr><td class='k'>{html.escape(k)}</td><td>{n}</td></tr>" for k, n in pairs) or "<tr><td>-</td><td>0</td></tr>"

    doc = f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>India Accident News Monitor</title><style>
 body{{font:15px/1.5 system-ui,sans-serif;margin:0;background:#f6f7f9;color:#1a1a1a}}
 .wrap{{max-width:960px;margin:0 auto;padding:24px 16px}} h1{{font-size:22px;margin:0 0 4px}} h2{{font-size:16px;margin:26px 0 8px}}
 .sub{{color:#666;font-size:13px;margin-bottom:16px}}
 .note{{background:#fff8e6;border:1px solid #f0e2b6;border-radius:10px;padding:12px 16px;font-size:13px;color:#5a4b16;margin-bottom:18px}}
 .cards{{display:flex;gap:12px;flex-wrap:wrap}} .card{{background:#fff;border:1px solid #e3e5e9;border-radius:10px;padding:14px 18px;flex:1;min-width:100px}}
 .card .n{{font-size:24px;font-weight:600}} .card .l{{font-size:12px;color:#666}}
 table{{width:100%;border-collapse:collapse;background:#fff;border:1px solid #e3e5e9;border-radius:10px;overflow:hidden;margin-top:6px}}
 th,td{{padding:7px 9px;text-align:right;border-bottom:1px solid #eef0f2;font-variant-numeric:tabular-nums;font-size:13px}}
 thead th{{background:#f0f2f5;font-size:11px;text-transform:uppercase;letter-spacing:.03em}}
 tbody th,td.k{{text-align:left}} td.k{{font-weight:400}} tbody th{{font-weight:600}} td.tot{{font-weight:600;background:#fafbfc}}
 .two{{display:flex;gap:16px;flex-wrap:wrap}} .two>div{{flex:1;min-width:260px}}
</style></head><body><div class="wrap">
<h1>India Accident News Monitor</h1><div class="sub">Last updated {last} &middot; infrastructure &amp; transport only &middot; natural calamities excluded</div>
<div class="note"><b>News-mention counts, not official totals.</b> Cross-language duplicates are merged where facts align (some slip through). Natural calamities (floods, landslides, quakes, etc.) are filtered out. Authoritative figures: MoRTH, NCRB, DGFASLI. Images are publisher links.</div>
<div class="cards">
 <div class="card"><div class="n">{total}</div><div class="l">unique events</div></div>
 <div class="card"><div class="n">{merged}</div><div class="l">duplicates merged</div></div>
 <div class="card"><div class="n">{total_raw}</div><div class="l">raw records</div></div>
 <div class="card"><div class="n">{with_img}</div><div class="l">with image</div></div>
 <div class="card"><div class="n">{with_cause}</div><div class="l">with stated cause</div></div>
 <div class="card"><div class="n">{len(periods)}</div><div class="l">months</div></div>
</div>
<h2>Monthly unique events by category</h2>
<table><thead><tr><th style="text-align:left">Month</th>{head}<th>Total</th></tr></thead><tbody>{body}</tbody></table>
<h2>Top reported causes <span style="font-weight:400;color:#888;font-size:12px">(as-reported / preliminary, not investigated)</span></h2>
<table><tbody>{rows_html(top_counts(conn,'cause'))}</tbody></table>
<div class="two">
 <div><h2>Top cities</h2><table><tbody>{rows_html(top_counts(conn,'cities'))}</tbody></table></div>
 <div><h2>Top highways</h2><table><tbody>{rows_html(top_counts(conn,'highways'))}</tbody></table></div>
</div></div></body></html>"""
    with open(path, "w", encoding="utf-8") as f:
        f.write(doc)


# ===========================================================================
# MAIN
# ===========================================================================
def run():
    conn = sqlite3.connect(DB_PATH)
    init_db(conn)
    ebudget, tbudget = MAX_ENRICH_PER_RUN, MAX_TRANSLATE_PER_RUN
    total_new = 0
    dead = []

    for code, (label, ceid) in EDITIONS.items():
        for q in GN_QUERIES.get(code, []):
            data, _ = http_get(feed_url(q, code, ceid))
            arts = parse_feed(data, label, q, prefilter=False)
            added, ebudget, tbudget = store(conn, arts, ebudget, tbudget)
            total_new += added
            print(f"[GN {label}] {q!r}: {len(arts)} items, {added} kept")
            time.sleep(1)

    for label, url in NEWSPAPER_FEEDS:
        data, _ = http_get(url)
        if data is None:
            dead.append(url)
            print(f"[PAPER {label}] DEAD: {url}")
            continue
        arts = parse_feed(data, label, url, prefilter=True)
        added, ebudget, tbudget = store(conn, arts, ebudget, tbudget)
        total_new += added
        print(f"[PAPER {label}] {url}: {len(arts)} candidate items, {added} kept")
        time.sleep(1)

    backfill_translations(conn, tbudget)
    rededupe(conn)

    n = export_articles_csv(conn)
    export_summary_csv(conn, "%Y-%m", "monthly_summary.csv")
    export_summary_csv(conn, "%Y", "yearly_summary.csv")
    export_cause_summary_csv(conn)
    export_cause_trend_csv(conn)
    export_dashboard(conn)
    conn.close()
    print(f"\nDone. {total_new} new this run. {n} records total. "
          f"(translate left {tbudget}, enrich left {ebudget})")
    if dead:
        print("Dead feeds to fix/remove:", *dead, sep="\n  ")


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        # ---- categories ----
        assert detect_category("Flyover collapses in Mumbai, 5 dead") == "construction_infra"
        assert detect_category("School bus overturns near Pune") == "bus"
        assert detect_category("Truck rams into cars on NH-19") == "cargo"
        assert detect_category("Train derails near Kanpur") == "train"
        assert detect_category("Plane crashes near Delhi airport") == "flight"
        assert detect_category("Pedestrian run over by speeding SUV") == "pedestrian"
        assert detect_category("Two-wheeler skids on highway, rider dead") == "traffic"
        assert detect_category("Boiler blast at chemical factory") == "industrial"
        assert detect_category("Minister opens new hospital") is None
        # ---- natural exclusion ----
        assert classify("20 dead as floods hit Kerala") is None
        assert classify("Building collapses after cloudburst, 5 dead") is None  # STRICT default
        assert classify("Bus falls into river on NH-48, 8 dead") == "bus"
        # ---- casualty extraction incl Devanagari digits ----
        assert extract_counts("3 killed, 2 injured in bus crash") == (3, 2)
        d, i = extract_counts("बस दुर्घटना में \u0969 की मौत, \u0968 घायल"); assert (d, i) == (3, 2)
        # ---- reported-cause extraction ----
        assert "trench_excavation_collapse" in extract_causes("Trench collapses at highway construction site in Bengaluru, 2 workers dead")
        c2 = extract_causes("Speeding car loses control in dense fog on NH-48, 3 dead")
        assert "overspeeding" in c2 and "fog_poor_visibility" in c2
        assert "gas_leak" in extract_causes("Gas leak at chemical factory injures 12")
        assert extract_causes("New expressway inaugurated by minister") == ""  # no stated cause
        print("cause sample:", extract_causes("Bus overturns after tyre burst on wet road near Pune"))
        # ---- translation-assisted cross-language dedup ----
        _MOCK_TRANSLATE = lambda t: ("3 killed 2 injured in bus accident on NH-48 near Pune"
                                     if "\u0985" in t or "\u0995" in t or "\u09ac" in t else "")
        conn = sqlite3.connect(":memory:"); init_db(conn)
        A = parse_feed(("<rss><channel><item><title>3 killed, 2 injured in bus accident on NH-48 near Pune - TOI</title>"
                        "<link>http://a</link><pubDate>Fri, 15 Aug 2026 06:00:00 GMT</pubDate></item></channel></rss>").encode(),
                       "English", "q")
        store(conn, A, 0, 0)
        # an ASSAMESE article (no Google News edition) - only translation makes it comparable
        B = parse_feed(("<rss><channel><item><title>\u0985\u09b8\u09ae\u09c0\u09df\u09be \u0995\u09ac\u09b0 - "
                        "NH-48 \u09ac\u09be\u09b8 \u09a6\u09c1\u09b0\u09cd\u0998\u099f\u09a8\u09be</title>"
                        "<link>http://b</link><pubDate>Fri, 15 Aug 2026 09:00:00 GMT</pubDate></item></channel></rss>").encode(),
                       "Assamese", "paper")
        store(conn, B, 0, 5)
        rows = conn.execute("SELECT title,category,is_duplicate,deaths,injured,cities,highways,translated FROM articles").fetchall()
        for r in rows:
            print("  ", r)
        uniq = conn.execute("SELECT COUNT(*) FROM articles WHERE is_duplicate=0").fetchone()[0]
        assert uniq == 1, "Assamese bus report should merge with English via translation"
        _MOCK_TRANSLATE = None
        print("SELF-TEST PASSED")
    else:
        run()
