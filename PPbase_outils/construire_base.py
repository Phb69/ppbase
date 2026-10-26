#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PPbase v2 : construit les bases routieres regionales (limitations de vitesse) pour PermisPointsApp.
Un fichier par region (routes-<region>.bin) + un manifeste version.json (format 2).

Usage (une seule fois : pip install osmium) :
    python construire_base.py                      # menu interactif de choix des regions
    python construire_base.py --regions rhone-alpes bourgogne
    python construire_base.py --france             # toute la France, outre-mer compris (27 regions)
    python construire_base.py --metropole          # France metropolitaine seule (22 regions)
    python construire_base.py --liste              # affiche les noms de regions
  Options : --force (reconstruit meme si a jour)  --sans-ftp  --garder-pbf
  Si ftp.ini existe a cote du script, les fichiers nouveaux ou modifies sont envoyes par FTP.
  Un extrait deja telecharge a la main (ex. sortie/pbf/rhone-alpes-261024.osm.pbf) est reutilise.

Format PPB1 (little endian) :
  'PPB1' | date_unix i64 | taille_tuile u32 (en 1e-5 deg) | nb_tuiles u32
  repertoire : nb_tuiles x (tx i32, ty i32, offset u32, longueur u32)   (offset depuis le debut du fichier)
  blobs : deflate brut ; contenu = nb_voies u32, puis par voie :
          vitesse u8 | nb_points u16 | lat0 i32 | lon0 i32 | (dlat i16, dlon i16) x (nb_points-1)
  coordonnees en 1e-5 degre (~1 m). tuile = (floor(lat/taille), floor(lon/taille)).

Manifeste version.json :
  {"format": 2, "genere": "...", "regions": {"<cle>": {"label","fichier","date","date_unix","taille","sha256","voies","tuiles"}}}
"""
import sys, os, re, struct, zlib, json, hashlib, time, math, calendar, urllib.request, ftplib, getpass, configparser
import osmium

TAILLE_TUILE = 5000          # 0.05 degre (~5.5 km)
ECHELLE = 100000.0           # 1e-5 degre
PAS_MAX = 1000.0             # metres : on ajoute des points sur les longs segments
URL_GEOFABRIK = "https://download.geofabrik.de/europe/france/{cle}-latest.osm.pbf"
URL_VERSION = "https://phb69.pages-perso.free.fr/PPbase/version.json"

# Regions de France metropolitaine (decoupage Geofabrik, anciennes regions).
REGIONS = {
    "alsace": "Alsace", "aquitaine": "Aquitaine", "auvergne": "Auvergne",
    "basse-normandie": "Basse-Normandie", "bourgogne": "Bourgogne", "bretagne": "Bretagne",
    "centre": "Centre-Val de Loire", "champagne-ardenne": "Champagne-Ardenne", "corse": "Corse",
    "franche-comte": "Franche-Comté", "haute-normandie": "Haute-Normandie", "ile-de-france": "Île-de-France",
    "languedoc-roussillon": "Languedoc-Roussillon", "limousin": "Limousin", "lorraine": "Lorraine",
    "midi-pyrenees": "Midi-Pyrénées", "nord-pas-de-calais": "Nord-Pas-de-Calais",
    "pays-de-la-loire": "Pays de la Loire", "picardie": "Picardie", "poitou-charentes": "Poitou-Charentes",
    "provence-alpes-cote-d-azur": "Provence-Alpes-Côte d'Azur", "rhone-alpes": "Rhône-Alpes",
}
OUTRE_MER = {
    "guadeloupe": "Guadeloupe", "guyane": "Guyane", "martinique": "Martinique",
    "mayotte": "Mayotte", "reunion": "La Réunion",
}
METROPOLE = list(REGIONS)          # 22 regions metropolitaines
REGIONS.update(OUTRE_MER)          # catalogue complet : 27 regions
PAR_DEFAUT = ["auvergne", "rhone-alpes", "provence-alpes-cote-d-azur", "bourgogne"]

VITESSES_FR = {
    "fr:urban": 50, "fr:rural": 80, "fr:zone30": 30, "fr:zone20": 20,
    "fr:motorway": 130, "fr:trunk": 110, "fr:walk": 6,
}
HIGHWAYS_OK = {
    "motorway", "motorway_link", "trunk", "trunk_link", "primary", "primary_link",
    "secondary", "secondary_link", "tertiary", "tertiary_link", "unclassified",
    "residential", "living_street", "service", "road",
}


def parse_vitesse(v):
    if not v:
        return None
    v = v.strip().lower()
    if v in VITESSES_FR:
        return VITESSES_FR[v]
    if v.isdigit():
        n = int(v)
        return n if 5 <= n <= 150 else None
    return None  # mph, listes, "none", etc. : ignores


class Collecteur(osmium.SimpleHandler):
    def __init__(self, tuiles):
        super().__init__()
        self.tuiles = tuiles
        self.nb = 0

    def way(self, w):
        t = w.tags
        if t.get("highway") not in HIGHWAYS_OK:
            return
        vit = parse_vitesse(t.get("maxspeed"))
        if vit is None:
            return
        pts = []
        for n in w.nodes:
            if not n.location.valid():
                return
            pts.append((round(n.location.lat * ECHELLE), round(n.location.lon * ECHELLE)))
        if len(pts) < 2:
            return
        pts = densifier(pts)
        for morceau in decouper(pts):
            self.ajouter(vit, morceau)

    def ajouter(self, vit, pts):
        cles = set()
        for lat, lon in pts:
            cles.add((lat // TAILLE_TUILE, lon // TAILLE_TUILE))
        enc = bytearray(struct.pack("<BH", vit, len(pts)))
        enc += struct.pack("<ii", pts[0][0], pts[0][1])
        for i in range(1, len(pts)):
            enc += struct.pack("<hh", pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1])
        for c in cles:
            self.tuiles.setdefault(c, []).append(bytes(enc))
        self.nb += 1


def densifier(pts):
    """Insere des points sur les segments de plus de PAS_MAX metres."""
    sortie = [pts[0]]
    for i in range(1, len(pts)):
        a, b = sortie[-1], pts[i]
        dlat = (b[0] - a[0]) / ECHELLE * 111000.0
        dlon = (b[1] - a[1]) / ECHELLE * 111000.0 * math.cos(math.radians(a[0] / ECHELLE))
        dist = math.hypot(dlat, dlon)
        n = int(dist // PAS_MAX)
        for k in range(1, n + 1):
            f = k / (n + 1)
            sortie.append((round(a[0] + (b[0] - a[0]) * f), round(a[1] + (b[1] - a[1]) * f)))
        sortie.append(b)
    return sortie


def decouper(pts):
    """Coupe si un delta depasse int16 ou si plus de 65000 points."""
    morceau = [pts[0]]
    for p in pts[1:]:
        q = morceau[-1]
        if abs(p[0] - q[0]) > 32000 or abs(p[1] - q[1]) > 32000 or len(morceau) >= 65000:
            if len(morceau) >= 2:
                yield morceau
            morceau = [p]
        else:
            morceau.append(p)
    if len(morceau) >= 2:
        yield morceau



def date_depuis_nom(nom):
    """Extrait la date AAMMJJ d'un nom comme rhone-alpes-261024.osm.pbf -> (timestamp UTC, 'AAAA-MM-JJ')."""
    m = re.search(r"-(\d{2})(\d{2})(\d{2})\.osm\.pbf$", nom)
    if not m:
        return None
    aa, mm, jj = int(m.group(1)), int(m.group(2)), int(m.group(3))
    return calendar.timegm((2000 + aa, mm, jj, 0, 0, 0)), f"{2000+aa:04d}-{mm:02d}-{jj:02d}"


def resoudre_latest(url):
    """Suit la redirection de ...-latest.osm.pbf (requete HEAD, rien n'est telecharge)
    et retourne l'URL datee reelle."""
    req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "PPbase-builder/1.0"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return r.geturl()


URL_VERSION = "https://phb69.pages-perso.free.fr/PPbase/version.json"


def lire_config_ftp(ici):
    """ftp.ini (a cote du script) : [ftp] serveur, utilisateur, dossier [, motdepasse].
    Le mot de passe est demande au clavier s'il n'est pas dans le fichier (recommande)."""
    chemin = os.path.join(ici, "ftp.ini")
    if not os.path.exists(chemin):
        return None
    cp = configparser.ConfigParser()
    cp.read(chemin, encoding="utf-8")
    if "ftp" not in cp:
        return None
    c = cp["ftp"]
    return {
        "serveur": c.get("serveur", "ftpperso.free.fr").strip(),
        "utilisateur": c.get("utilisateur", "").strip(),
        "port": c.getint("port", 21),
        "dossier": c.get("dossier", "PPbase").strip(),
        "motdepasse": c.get("motdepasse", "").strip(),
    }


def connecter_ftp(cfg):
    mdp = cfg["motdepasse"] or getpass.getpass(f"Mot de passe FTP de {cfg['utilisateur']} : ")
    try:
        ftp = ftplib.FTP_TLS(timeout=60)
        ftp.connect(cfg["serveur"], cfg["port"])
        ftp.login(cfg["utilisateur"], mdp)
        ftp.prot_p()
        print("  connexion FTP chiffree (FTPS)")
    except Exception as e:
        print(f"  FTPS indisponible ({e}) : connexion FTP classique (non chiffree)")
        ftp = ftplib.FTP(timeout=60)
        ftp.connect(cfg["serveur"], cfg["port"])
        ftp.login(cfg["utilisateur"], mdp)
    return ftp


def envoyer_ftp(sortie, cfg, manifeste, a_envoyer):
    """Envoie les .bin listes (a_envoyer = {cle: sha}) puis version.json (en dernier), puis verifie."""
    print(f"Envoi FTP vers {cfg['serveur']}/{cfg['dossier']} ...")
    ftp = connecter_ftp(cfg)
    try:
        for part in [p for p in cfg["dossier"].split("/") if p]:
            try:
                ftp.cwd(part)
            except ftplib.error_perm:
                ftp.mkd(part)
                ftp.cwd(part)
        noms = [manifeste["regions"][k]["fichier"] for k in a_envoyer] + ["version.json"]
        for nom in noms:
            chemin = os.path.join(sortie, nom)
            taille = os.path.getsize(chemin)
            print(f"  {nom} ({taille/1e6:.1f} Mo)...")
            with open(chemin, "rb") as f:
                ftp.storbinary(f"STOR {nom}", f)
            distant = ftp.size(nom)
            if distant is not None and distant != taille:
                raise RuntimeError(f"{nom} : taille distante {distant} differente de {taille}")
    finally:
        try:
            ftp.quit()
        except Exception:
            pass
    try:
        req = urllib.request.Request(URL_VERSION + "?t=" + str(int(time.time())), headers={"User-Agent": "PPbase-builder/2.0"})
        with urllib.request.urlopen(req, timeout=30) as r:
            vu = json.loads(r.read().decode("utf-8"))
        ok = all(vu.get("regions", {}).get(k, {}).get("sha256") == manifeste["regions"][k]["sha256"] for k in a_envoyer)
        print("  Verification OK : le site sert bien les nouvelles versions." if ok else
              "  ATTENTION : le site sert encore d'anciennes versions (cache ?). Reessaie dans quelques minutes.")
    except Exception as e:
        print(f"  Verification HTTPS impossible ({e}) : verifie manuellement {URL_VERSION}")
    marque = os.path.join(sortie, "televerse.json")
    deja = json.load(open(marque, encoding="utf-8")) if os.path.exists(marque) else {}
    deja.update(a_envoyer)
    json.dump(deja, open(marque, "w", encoding="utf-8"))
    print("Envoi termine.")


def telecharger(url, dest):
    print(f"Telechargement {url} ...")
    def prog(b, bs, total):
        if total > 0 and b % 200 == 0:
            print(f"\r  {min(100, b * bs * 100 // total)} %", end="", flush=True)
    urllib.request.urlretrieve(url, dest, prog)
    print()


def ecrire(tuiles, chemin, date_ts):
    blobs = {}
    for cle in sorted(tuiles):
        corps = struct.pack("<I", len(tuiles[cle])) + b"".join(tuiles[cle])
        c = zlib.compressobj(9, zlib.DEFLATED, -15)
        blobs[cle] = c.compress(corps) + c.flush()
    entete = 4 + 8 + 4 + 4
    taille_rep = len(blobs) * 16
    offset = entete + taille_rep
    rep = bytearray()
    for cle in sorted(blobs):
        rep += struct.pack("<iiII", cle[0], cle[1], offset, len(blobs[cle]))
        offset += len(blobs[cle])
    with open(chemin, "wb") as f:
        f.write(b"PPB1")
        f.write(struct.pack("<qII", date_ts, TAILLE_TUILE, len(blobs)))
        f.write(rep)
        for cle in sorted(blobs):
            f.write(blobs[cle])


def construire_region(cle, chemin_pbf, date_ts, sortie):
    tuiles = {}
    print(f"  lecture de {os.path.basename(chemin_pbf)} (quelques minutes)...")
    h = Collecteur(tuiles)
    h.apply_file(chemin_pbf, locations=True, idx="flex_mem")
    fichier = f"routes-{cle}.bin"
    chemin = os.path.join(sortie, fichier)
    ecrire(tuiles, chemin, date_ts)
    data = open(chemin, "rb").read()
    return {
        "label": REGIONS.get(cle, cle),
        "fichier": fichier,
        "date": time.strftime("%Y-%m-%d", time.gmtime(date_ts)),
        "date_unix": date_ts,
        "taille": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
        "voies": h.nb,
        "tuiles": len(tuiles),
    }


def choisir_regions(args):
    if "--liste" in args:
        for k, v in REGIONS.items():
            print(f"  {k:30s} {v}")
        sys.exit(0)
    if "--france" in args:
        return list(REGIONS)             # les 27 regions (metropole + outre-mer)
    if "--metropole" in args:
        return list(METROPOLE)
    if "--regions" in args:
        i = args.index("--regions")
        cles = []
        for a in args[i + 1:]:
            if a.startswith("--"):
                break
            cles.append(a)
        inconnues = [c for c in cles if c not in REGIONS]
        if inconnues or not cles:
            sys.exit(f"Region(s) inconnue(s) : {inconnues or 'aucune indiquee'}. Voir --liste.")
        return cles
    if not sys.stdin.isatty():
        return list(PAR_DEFAUT)
    cles = list(REGIONS)
    print("Regions disponibles ([*] = proposees par defaut) :")
    for n, k in enumerate(cles, 1):
        print(f"  {n:2d}. [{'*' if k in PAR_DEFAUT else ' '}] {REGIONS[k]}")
    rep = input("Numeros separes par des espaces, 't' = toute la France (27), 'm' = metropole (22), Entree = defaut : ").strip().lower()
    if not rep:
        return list(PAR_DEFAUT)
    if rep in ("t", "tout", "toutes", "france"):
        return cles
    if rep in ("m", "metropole", "métropole"):
        return list(METROPOLE)
    choix = []
    for p in re.split(r"[ ,;]+", rep):
        if p.isdigit() and 1 <= int(p) <= len(cles):
            choix.append(cles[int(p) - 1])
    if not choix:
        sys.exit("Aucun choix valide.")
    return choix


def main():
    args = sys.argv[1:]
    ici = os.path.dirname(os.path.abspath(__file__))
    sortie = os.path.join(ici, "sortie")
    dossier_pbf = os.path.join(sortie, "pbf")
    os.makedirs(dossier_pbf, exist_ok=True)
    forcer = "--force" in args
    garder = "--garder-pbf" in args
    cfg_ftp = None if "--sans-ftp" in args else lire_config_ftp(ici)

    regions = choisir_regions(args)
    print("Regions retenues : " + ", ".join(REGIONS[r] for r in regions))

    chemin_manifeste = os.path.join(sortie, "version.json")
    manifeste = {"format": 2, "regions": {}}
    if os.path.exists(chemin_manifeste):
        try:
            m = json.load(open(chemin_manifeste, encoding="utf-8"))
            if m.get("format") == 2:
                manifeste = m
        except Exception:
            pass
    # on ne garde au manifeste que les regions dont le .bin existe encore
    manifeste["regions"] = {k: v for k, v in manifeste["regions"].items()
                            if os.path.exists(os.path.join(sortie, v["fichier"]))}

    for cle in regions:
        print(f"[{REGIONS[cle]}]")
        url = URL_GEOFABRIK.format(cle=cle)
        try:
            reel = resoudre_latest(url)
        except Exception as e:
            print(f"  ERREUR : impossible de joindre {url} ({e}). Region ignoree.")
            continue
        nom = os.path.basename(reel.split("?")[0])
        d = date_depuis_nom(nom)
        if d is None:
            print(f"  ERREUR : date illisible dans {reel}. Region ignoree.")
            continue
        date_ts, date_txt = d
        actuel = manifeste["regions"].get(cle)
        if actuel and actuel["date_unix"] == date_ts and not forcer:
            print(f"  deja a jour (donnees OSM du {date_txt})")
            continue
        pbf = os.path.join(dossier_pbf, nom)
        if not os.path.exists(pbf):
            telecharger(reel, pbf)
        try:
            manifeste["regions"][cle] = construire_region(cle, pbf, date_ts, sortie)
        except Exception as e:
            print(f"  ERREUR pendant la construction : {e}")
            continue
        r = manifeste["regions"][cle]
        print(f"  OK : {r['taille']/1e6:.1f} Mo, {r['voies']} voies (donnees OSM du {date_txt})")
        manifeste["genere"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        json.dump(manifeste, open(chemin_manifeste, "w", encoding="utf-8"), indent=2, ensure_ascii=False)
        if not garder:
            try:
                os.remove(pbf)
            except OSError:
                pass

    if not manifeste["regions"]:
        sys.exit("Aucune base disponible.")
    manifeste["genere"] = manifeste.get("genere") or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    manifeste["licence"] = "ODbL 1.0 - https://opendatacommons.org/licenses/odbl/1-0/"
    manifeste["attribution"] = "© OpenStreetMap contributors - https://www.openstreetmap.org/copyright"
    manifeste["source"] = "Extraits Geofabrik (https://download.geofabrik.de/)"
    json.dump(manifeste, open(chemin_manifeste, "w", encoding="utf-8"), indent=2, ensure_ascii=False)
    total = sum(v["taille"] for v in manifeste["regions"].values())
    print(f"Bases disponibles : {len(manifeste['regions'])} region(s), {total/1e6:.1f} Mo au total")

    if cfg_ftp:
        marque = os.path.join(sortie, "televerse.json")
        deja = json.load(open(marque, encoding="utf-8")) if os.path.exists(marque) else {}
        a_envoyer = {k: v["sha256"] for k, v in manifeste["regions"].items() if deja.get(k) != v["sha256"]}
        if a_envoyer or not deja:
            envoyer_ftp(sortie, cfg_ftp, manifeste, a_envoyer)
        else:
            print("Tout est deja envoye sur le site : rien a faire.")
    else:
        print("Pas d'envoi FTP (ftp.ini absent ou --sans-ftp) : depose les routes-*.bin puis version.json dans PPbase/ sur ton site.")


if __name__ == "__main__":
    main()
