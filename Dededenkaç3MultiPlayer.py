import pygame
import math
import random
import sys
import socket
import threading
import json
import time
import hashlib
import base64

pygame.init()

WIDTH, HEIGHT = 360, 640
try:
    screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.SCALED | pygame.FULLSCREEN)
except Exception:
    info = pygame.display.Info()
    WIDTH = min(info.current_w, info.current_h)
    HEIGHT = max(info.current_w, info.current_h)
    screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.FULLSCREEN)

pygame.display.set_caption("3D Minecraft Köy Avı - Pro Multiplayer")
clock = pygame.time.Clock()

VIEW_H = int(HEIGHT * 0.70)
CENTER_X = WIDTH // 2
CENTER_Y = int(HEIGHT * 0.38)

font_title = pygame.font.SysFont("arial", int(WIDTH * 0.08), bold=True)
font_btn = pygame.font.SysFont("arial", int(WIDTH * 0.06), bold=True)
font_ui = pygame.font.SysFont("arial", int(WIDTH * 0.042), bold=True)
font_small = pygame.font.SysFont("arial", int(WIDTH * 0.032), bold=True)

# Kasmayı önleyen yazı önbelleği (Text Cache)
_text_cache = {}


def draw_text_fit(text, font, color, cx, cy, max_w):
    key = (text, id(font), color, int(max_w))
    surf = _text_cache.get(key)
    if surf is None:
        if len(_text_cache) > 300:
            _text_cache.clear()
        surf = font.render(text, True, color)
        w, h = surf.get_size()
        if w > max_w and w > 0:
            scale = max_w / float(w)
            surf = pygame.transform.smoothscale(surf, (max(1, int(w * scale)), max(1, int(h * scale))))
        _text_cache[key] = surf
    screen.blit(surf, (cx - surf.get_width() // 2, cy - surf.get_height() // 2))


STATE_MENU = "MENU"
STATE_HOST_PIN = "HOST_PIN"
STATE_JOIN_PIN = "JOIN_PIN"
STATE_GAME = "GAME"
STATE_GAMEOVER = "GAMEOVER"
STATE_WIN = "WIN"
game_state = STATE_MENU

_k_adm_cost = (100 << 6) + (25 << 2)
_k_med_cost = (75 << 1)

net_mode = None
net_socket = None

# Çok oyunculu senkronizasyon verileri
remote_player_pos = {
    "x": 0.0, "z": -5.0, "yaw": 0.0, "pitch": 0.0,
    "weapon": "PISTOL", "money": 0, "moving": False,
    "shoot_seq": 0, "active": False
}
remote_player_target = {
    "x": 0.0, "z": -5.0, "yaw": 0.0, "pitch": 0.0,
    "weapon": "PISTOL", "money": 0, "moving": False,
    "shoot_seq": 0
}
remote_anim = 0.0
last_remote_shoot_seq = 0
my_shoot_seq = 0
is_local_moving = False

input_pin_text = "1453"
input_host_ip = "10.32.1.45"
active_input_field = "PIN"

ui_click_cooldown = 0

play_btn_rect = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.38), int(WIDTH * 0.64), int(HEIGHT * 0.08))
host_btn_rect = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.48), int(WIDTH * 0.64), int(HEIGHT * 0.08))
join_btn_rect = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.58), int(WIDTH * 0.64), int(HEIGHT * 0.08))

pin_box_rect = pygame.Rect(int(WIDTH * 0.12), int(HEIGHT * 0.28), int(WIDTH * 0.76), int(HEIGHT * 0.065))
ip_box_rect = pygame.Rect(int(WIDTH * 0.12), int(HEIGHT * 0.38), int(WIDTH * 0.76), int(HEIGHT * 0.065))
pin_connect_btn = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.88), int(WIDTH * 0.64), int(HEIGHT * 0.075))

keyboard_buttons = []
keys_layout = [
    ["1", "2", "3", "4", "5", "6", "7", "8", "9", "0"],
    ["Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P"],
    ["A", "S", "D", "F", "G", "H", "J", "K", "L", "."],
    ["Z", "X", "C", "V", "B", "N", "M", "SİL"]
]

kb_start_y = int(HEIGHT * 0.48)
kb_row_h = int(HEIGHT * 0.085)
for r_idx, row in enumerate(keys_layout):
    r_w = len(row)
    btn_w = int((WIDTH * 0.90) / r_w)
    start_x = int(WIDTH * 0.05)
    for c_idx, char in enumerate(row):
        bx = start_x + c_idx * btn_w + 2
        by = kb_start_y + r_idx * kb_row_h + 2
        bw = btn_w - 4
        bh = kb_row_h - 4
        keyboard_buttons.append((pygame.Rect(bx, by, bw, bh), char))


def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


def pin_to_port(pin_str):
    try:
        return 10000 + (int(pin_str) % 50000)
    except Exception:
        return 15432


def _parse_incoming_stream(recv_buf):
    global remote_player_target, remote_player_pos
    if "\n" in recv_buf:
        lines = recv_buf.split("\n")
        recv_buf = lines[-1]
        for line in reversed(lines[:-1]):
            line = line.strip()
            if line:
                try:
                    pkt = json.loads(line)
                    remote_player_target["x"] = float(pkt.get("x", 0.0))
                    remote_player_target["z"] = float(pkt.get("z", -5.0))
                    remote_player_target["yaw"] = float(pkt.get("yaw", 0.0))
                    remote_player_target["pitch"] = float(pkt.get("pitch", 0.0))
                    remote_player_target["weapon"] = pkt.get("weapon", "PISTOL")
                    remote_player_target["money"] = int(pkt.get("money", 0))
                    remote_player_target["moving"] = bool(pkt.get("moving", False))
                    remote_player_target["shoot_seq"] = int(pkt.get("shoot_seq", 0))
                    if not remote_player_pos["active"]:
                        remote_player_pos["x"] = remote_player_target["x"]
                        remote_player_pos["z"] = remote_player_target["z"]
                        remote_player_pos["yaw"] = remote_player_target["yaw"]
                        remote_player_pos["active"] = True
                    break
                except Exception:
                    pass
    return recv_buf


def _build_my_packet():
    return (json.dumps({
        "x": round(cam_x, 3),
        "z": round(cam_z, 3),
        "yaw": round(cam_yaw, 3),
        "pitch": round(cam_pitch, 3),
        "weapon": current_weapon if has_gun else "NONE",
        "money": _rt_wallet.get(),
        "moving": is_local_moving,
        "shoot_seq": my_shoot_seq
    }) + "\n").encode()


def network_server_thread(port):
    global net_socket
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        server.bind(("0.0.0.0", port))
        server.listen(1)
        while True:
            conn, addr = server.accept()
            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            conn.setblocking(False)
            net_socket = conn
            recv_buf = ""
            while True:
                try:
                    data = conn.recv(4096)
                    if not data:
                        break
                    recv_buf += data.decode("utf-8", errors="ignore")
                    recv_buf = _parse_incoming_stream(recv_buf)
                except BlockingIOError:
                    pass
                except Exception:
                    break

                try:
                    conn.sendall(_build_my_packet())
                except BlockingIOError:
                    pass
                except Exception:
                    break

                time.sleep(0.025)
    except Exception:
        pass


def network_client_thread(ip, port):
    global net_socket
    while True:
        client = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        client.settimeout(3.0)
        try:
            client.connect((ip.strip(), port))
            client.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            client.setblocking(False)
            net_socket = client
            recv_buf = ""
            while True:
                try:
                    client.sendall(_build_my_packet())
                except BlockingIOError:
                    pass
                except Exception:
                    break

                try:
                    data = client.recv(4096)
                    if not data:
                        break
                    recv_buf += data.decode("utf-8", errors="ignore")
                    recv_buf = _parse_incoming_stream(recv_buf)
                except BlockingIOError:
                    pass
                except Exception:
                    break

                time.sleep(0.025)
        except Exception:
            time.sleep(1.0)


def _gl_wep_shader(_w_id):
    _w_mat = {
        "PISTOL": ((19 ^ 19), (26 >> 1), ((5 << 2) / 20.0), False, 0.005, 1.0, 0.0),
        "AK47": ((25 << 4), (10 >> 1), ((7 << 2) / 20.0), True, 0.022, 0.65, 0.0),
        "RPG": ((225 << 2), (9 << 2), float(3 << 2), False, 0.0, 1.8, float(3 << 1)),
        "MINIGUN": ((375 << 2), (4 >> 1), ((6 << 2) / 20.0), True, 0.042, 0.35, 0.0)
    }
    return _w_mat[_w_id]


WEAPONS = {
    "PISTOL": {"name": "Tabanca", "tracer_col": (255, 230, 120), "desc": "Standart yarı otomatik"},
    "AK47": {"name": "AK-47 Tüfek", "tracer_col": (255, 200, 70), "desc": "Seri taramalı, yüksek hasar"},
    "RPG": {"name": "RPG Roketatar", "tracer_col": (255, 90, 30), "desc": "Devasa alan patlaması!"},
    "MINIGUN": {"name": "Minigun", "tracer_col": (255, 245, 150), "desc": "Dönen namlulu mermi yağmuru!"}
}
WEAPON_ORDER = ["PISTOL", "AK47", "RPG", "MINIGUN"]


def _shd_lod_matrix(_tag):
    _m = {
        "ZOMBIE": ((50 >> 1), (40 / 20.0), (1.9, 2.5), 20.0, 0.0, 0.0),
        "SKELETON": ((5 << 3), (36 / 20.0), (1.8, 2.3), 12.0, 15.0, 0.0),
        "CREEPER": ((110 >> 1), (48 / 20.0), (2.3, 2.9), 46.0, 0.0, 4.5),
        "PILLAGER": ((5 << 4), (70 / 20.0), (2.3, 3.0), 42.0, 0.0, 0.0),
        "WARDEN": ((125 << 4), float(125 << 1), (2.6, 2.9), 90.0, 28.0, 0.0)
    }
    return _m[_tag]


ENEMY_TYPES = {
    "ZOMBIE": {"name": "Zombi"},
    "SKELETON": {"name": "İskelet"},
    "CREEPER": {"name": "Creeper"},
    "PILLAGER": {"name": "Pillager"},
    "WARDEN": {"name": "WARDEN"}
}

cam_x, cam_y, cam_z = 0.0, 1.75, -6.5
cam_yaw = 0.0
cam_pitch = 0.0
FOV_ANGLE = math.radians(72.0)
FOV = (WIDTH * 0.5) / math.tan(FOV_ANGLE * 0.5) * 1.35
NEAR_PLANE = 0.25
FAR_PLANE = 38.0

SKY_TOP_COLOR = (38, 78, 155)
FOG_COLOR = (68, 118, 185)
GRASS_BG_COLOR = (72, 150, 52)

cos_yaw, sin_yaw = 1.0, 0.0
cos_pitch, sin_pitch = 1.0, 0.0

has_gun = False
current_weapon = "PISTOL"
owned_weapons = {"PISTOL"}


class _RtSyncState:
    """Kaynak dosyada düz bir sayı olarak durmasın diye bakiye burada
    her yazımda değişen bir maskeyle saklanır ve ayrı bir sağlama
    değeriyle doğrulanır. Sağlama tutmazsa (bellekten doğrudan
    değiştirilmişse) bakiye sıfırlanır.

    Multiplayer'da ağ thread'i (paket göndermek için) sürekli get()
    çağırırken ana thread aynı anda add()/try_spend() çağırabiliyor.
    Üç alanlık (_m, _e, _c) güncelleme tek seferde olmazsa ağ thread'i
    yarım kalmış bir durumu "kurcalanmış" sanıp bakiyeyi yanlışlıkla
    sıfırlayabilir. Bunu önlemek için her işlem RLock ile kilitleniyor."""
    __slots__ = ("_m", "_e", "_c", "_lock")

    def __init__(self):
        self._lock = threading.RLock()
        self._m = 0
        self._e = 0
        self._c = 0
        self._store(0)

    def _fingerprint(self, enc, mask):
        return (enc * 2654435761 + mask * 40503 + 0x9E3779B1) & 0xFFFFFFFF

    def _store(self, value):
        value = max(0, int(value))
        self._m = random.randint(1, 2 ** 31 - 1)
        self._e = value ^ self._m
        self._c = self._fingerprint(self._e, self._m)

    def get(self):
        with self._lock:
            if self._fingerprint(self._e, self._m) != self._c:
                self._store(0)
                return 0
            return self._e ^ self._m

    def set(self, value):
        with self._lock:
            self._store(value)

    def add(self, delta):
        with self._lock:
            self._store(self.get() + delta)

    def try_spend(self, amount):
        with self._lock:
            cur = self.get()
            if amount < 0 or cur < amount:
                return False
            self._store(cur - amount)
            return True


_rt_wallet = _RtSyncState()
warden_spawned = False
warden_active = False
warden_defeated = False
market_open = False
minigun_spin = 0.0

_adm_unlocked = False
_adm_open = False
_adm_oneshot = False
_adm_god = False
_adm_freeze = False
_adm_hyper = False
_dede_eliminated = False

# Admin panelinin gerçekten market üzerinden parayla açıldığını kanıtlayan
# gizli bir imza. _adm_unlocked'ı doğrudan True yapmak artık yetmiyor,
# bu imza da eşleşmek zorunda. _adm_proof_salt süreç başına rastgele
# üretilir, dosyada hiçbir yerde sabit olarak durmaz.
_adm_proof_salt = random.getrandbits(64)
_adm_proof = ""

dialog_active = False
dialog_text = "Selam evlat! Köyümüzü yaratıklar bastı,\nal bu silahı ve köyü kurtar!"
dialog_speaker = "Köylü Dede"
dialog_timer = 0
shoot_cooldown = 0
recoil_offset = 0.0
muzzle_light = 0.0
walk_bob = 0.0
_sys_vit_gauge = float(25 << 2)
score = 0
damage_flash = 0
screen_shake = 0.0
gameover_reason = "ÖLDÜN!"

troll_state = "NORMAL"
troll_timer = 0
troll_pos = [0.0, 0.0, 1.8]
troll_anim = 0.0

tracers = []
particles = []
enemy_arrows = []

sky_dots = [
    (random.randint(0, WIDTH), random.randint(0, int(VIEW_H * 0.6)), random.randint(2, 4), random.uniform(0, 6.28))
    for _ in range(25)
]

world_polygons = []
street_lights = []
world_colliders = []
old_man_screen_rect = pygame.Rect(0, 0, 0, 0)
enemies = []
spawn_timer = 0


# Beklenen tablo imzası: silah/düşman tablolarının doğru haliyle bir kez
# hesaplanmış sha256 özeti. Birileri yukarıdaki tabloları (hasar, can,
# ödül vb.) değiştirirse bu özet artık tutmaz. Üst/alt sınır yerine tam
# eşleşme arandığı için "sınırın hemen altında kal" türü atlatma işe yaramaz.
_EXPECTED_TABLE_DIGEST = "07a34765f651d2739017acb08137589d870a6f6301e3a483f4e0c4a086347" "252"
_TABLE_SALT = "kv9_mc_village_raid_integrity_v3_costs_included"
_ENEMY_ORDER_FOR_DIGEST = ("ZOMBIE", "SKELETON", "CREEPER", "PILLAGER", "WARDEN")


def _current_table_digest():
    parts = []
    for _wk in WEAPON_ORDER:
        parts.append(repr(_gl_wep_shader(_wk)))
    for _ek in _ENEMY_ORDER_FOR_DIGEST:
        parts.append(repr(_shd_lod_matrix(_ek)))
    # Market fiyatları (admin paneli, can paketi) de imzaya dahil: bunlar
    # önceki sürümde kontrol dışıydı, biri _k_adm_cost'u "1" yapıp admin
    # panelini 1 liraya açabiliyordu. Artık o değer değişince imza bozulur.
    parts.append(repr(_k_adm_cost))
    parts.append(repr(_k_med_cost))
    blob = "|".join(parts) + "|" + _TABLE_SALT
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


# Dosya kurcalanınca kalıcı olarak set edilen bayrak. Bir kez True olunca
# o oturumda geri "temiz"e dönmez; her karede tekrar denetlenir.
_gl_render_lock_state = False

# Ekrana basılan uyarı metinleri düz Türkçe cümle olarak dosyada durmasın
# diye XOR + base64 ile gizlendi, yalnızca gösterilirken çözülüyor.
_ENC_MSG_1 = "Ep7qFh96AxsKGxcbAxsZGxEOExQ="
_ENC_MSG_2 = "GxQOnup3GRIfGw56CR8Unup6AxsRGxYbHhN6d3oeFQkDG3oeH57EnuqfxA6e6gie6hYXnuqfxA=="


def _xd(_b64, _key=0x5A):
    _raw = base64.b64decode(_b64)
    return bytes(_b ^ _key for _b in _raw).decode("utf-8")


def _mint_adm_proof():
    return hashlib.sha256(f"{_adm_proof_salt}|adm_ok".encode("utf-8")).hexdigest()


def _adm_state_valid():
    """_adm_unlocked True iken geçerli bir satın-alma imzası yoksa, ya da
    panel hiç açılmamışken god/oneshot/freeze/hyper True olarak bulunmuşsa
    (kaynaktan doğrudan elle açılmış demektir) tüm admin güçlerini söker."""
    global _adm_unlocked, _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, _gl_render_lock_state
    tampered = False
    if _adm_unlocked and _adm_proof != _mint_adm_proof():
        tampered = True
    if (not _adm_unlocked) and (_adm_oneshot or _adm_god or _adm_freeze or _adm_hyper):
        tampered = True
    if tampered:
        _adm_unlocked = False
        _adm_open = False
        _adm_oneshot = False
        _adm_god = False
        _adm_freeze = False
        _adm_hyper = False
        _gl_render_lock_state = True
        _rt_wallet.set(0)
        return False
    return True


def _verify_gl_integrity():
    global _gl_render_lock_state
    if _current_table_digest() != _EXPECTED_TABLE_DIGEST:
        _rt_wallet.set(0)
        _gl_render_lock_state = True
        return False
    return not _gl_render_lock_state


def _sys_shader_cache_probe():
    # Ateş etme yolunda kullanılan ikinci, farklı isimli bir doğrulama.
    # Tek bir fonksiyonu bulup devre dışı bırakmak yetmesin diye kasıtlı
    # olarak tekrar ediyor.
    return _verify_gl_integrity()


def add_collider(cx, cz, w, d, max_y=5.5):
    hw = w * 0.5
    hd = d * 0.5
    world_colliders.append((cx - hw, cx + hw, cz - hd, cz + hd, max_y))


def resolve_collision(x, z, radius):
    x = max(-24.0, min(24.0, x))
    z = max(-21.0, min(41.5, z))

    for _ in range(2):
        for x1, x2, z1, z2, _ in world_colliders:
            cx = max(x1, min(x, x2))
            cz = max(z1, min(z, z2))
            dx = x - cx
            dz = z - cz
            dist_sq = dx * dx + dz * dz

            if dist_sq < radius * radius:
                if dist_sq > 1e-6:
                    dist = math.sqrt(dist_sq)
                    overlap = radius - dist
                    x += (dx / dist) * overlap
                    z += (dz / dist) * overlap
                else:
                    left_d = abs(x - x1)
                    right_d = abs(x2 - x)
                    back_d = abs(z - z1)
                    front_d = abs(z2 - z)
                    m = min(left_d, right_d, back_d, front_d)
                    if m == left_d:
                        x = x1 - radius
                    elif m == right_d:
                        x = x2 + radius
                    elif m == back_d:
                        z = z1 - radius
                    else:
                        z = z2 + radius
    return x, z


def is_point_inside_collider(x, z, y=1.0, margin=0.0):
    for x1, x2, z1, z2, max_y in world_colliders:
        if y <= max_y and (x1 - margin) <= x <= (x2 + margin) and (z1 - margin) <= z <= (z2 + margin):
            return True
    return False


def raycast_world_colliders(sx, sy, sz, dx, dy, dz, max_dist):
    closest_t = max_dist
    hit_wall = False

    for x1, x2, z1, z2, max_y in world_colliders:
        if abs(dx) < 1e-6:
            if sx < x1 or sx > x2:
                continue
            tx_min, tx_max = -1e9, 1e9
        else:
            inv_dx = 1.0 / dx
            t1 = (x1 - sx) * inv_dx
            t2 = (x2 - sx) * inv_dx
            tx_min, tx_max = min(t1, t2), max(t1, t2)

        if abs(dz) < 1e-6:
            if sz < z1 or sz > z2:
                continue
            tz_min, tz_max = -1e9, 1e9
        else:
            inv_dz = 1.0 / dz
            t1 = (z1 - sz) * inv_dz
            t2 = (z2 - sz) * inv_dz
            tz_min, tz_max = min(t1, t2), max(t1, t2)

        t_enter = max(tx_min, tz_min)
        t_exit = min(tx_max, tz_max)

        if t_enter <= t_exit and t_exit > 0.05:
            t_hit = t_enter if t_enter > 0.05 else t_exit
            if 0.05 < t_hit < closest_t:
                hit_y = sy + dy * t_hit
                if 0.0 <= hit_y <= max_y:
                    closest_t = t_hit
                    hit_wall = True

    return closest_t, hit_wall


def compute_normal_and_center(verts):
    n = len(verts)
    cx = sum(v[0] for v in verts) / n
    cy = sum(v[1] for v in verts) / n
    cz = sum(v[2] for v in verts) / n

    v0, v1, v2 = verts[0], verts[1], verts[2]
    ux, uy, uz = v1[0] - v0[0], v1[1] - v0[1], v1[2] - v0[2]
    vx, vy, vz = v2[0] - v0[0], v2[1] - v0[1], v2[2] - v0[2]
    nx = uy * vz - uz * vy
    ny = uz * vx - ux * vz
    nz = ux * vy - uy * vx
    length = math.sqrt(nx * nx + ny * ny + nz * nz)
    if length > 1e-6:
        nx, ny, nz = nx / length, ny / length, nz / length
    else:
        nx, ny, nz = 0.0, 1.0, 0.0
    return (cx, cy, cz), (nx, ny, nz)


def compute_static_light(center, normal, base_col, unlit):
    if unlit:
        return base_col

    cx, cy, cz = center
    nx, ny, nz = normal

    ambient = 0.64 + 0.22 * max(0.0, ny) + 0.12 * abs(nx) - 0.08 * abs(nz)
    r_acc = base_col[0] * ambient
    g_acc = base_col[1] * ambient
    b_acc = base_col[2] * ambient

    for lx, lz in street_lights:
        dx = lx - cx
        dy = 2.6 - cy
        dz = lz - cz
        dist_sq = dx * dx + dy * dy + dz * dz
        if dist_sq < 120.0:
            dist = math.sqrt(dist_sq)
            atten = 1.0 / (1.0 + 0.18 * dist + 0.05 * dist_sq)
            intensity = atten * 0.85
            r_acc += base_col[0] * intensity * 0.75 + 22.0 * intensity
            g_acc += base_col[1] * intensity * 0.55 + 12.0 * intensity
            b_acc += base_col[2] * intensity * 0.25

    return (
        min(255, max(0, int(r_acc))),
        min(255, max(0, int(g_acc))),
        min(255, max(0, int(b_acc)))
    )


def add_quad(p1, p2, p3, p4, color, unlit=False, layer_bias=0.0):
    verts = [p1, p2, p3, p4]
    center, normal = compute_normal_and_center(verts)
    lit_col = compute_static_light(center, normal, color, unlit)
    world_polygons.append((verts, lit_col, unlit, center, layer_bias))


def add_tri(p1, p2, p3, color, unlit=False, layer_bias=0.0):
    verts = [p1, p2, p3]
    center, normal = compute_normal_and_center(verts)
    lit_col = compute_static_light(center, normal, color, unlit)
    world_polygons.append((verts, lit_col, unlit, center, layer_bias))


def add_box(cx, y1, cz, w, h, d, col, top_col=None, unlit=False, layer_bias=0.0):
    x1, x2 = cx - w * 0.5, cx + w * 0.5
    z1, z2 = cz - d * 0.5, cz + d * 0.5
    y2 = y1 + h
    t_col = top_col if top_col else col

    add_quad((x1, y1, z1), (x2, y1, z1), (x2, y2, z1), (x1, y2, z1), col, unlit, layer_bias)
    add_quad((x2, y1, z2), (x1, y1, z2), (x1, y2, z2), (x2, y2, z2), col, unlit, layer_bias)
    add_quad((x1, y1, z2), (x1, y1, z1), (x1, y2, z1), (x1, y2, z2), col, unlit, layer_bias)
    add_quad((x2, y1, z1), (x2, y1, z2), (x2, y2, z2), (x2, y2, z1), col, unlit, layer_bias)
    add_quad((x1, y2, z1), (x2, y2, z1), (x2, y2, z2), (x1, y2, z2), t_col, unlit, layer_bias)


def create_mc_house(cx, cz, w, h, d, plank_col, roof_col):
    add_collider(cx, cz, w + 0.45, d + 0.45, max_y=h + h * 0.35)

    x1, x2 = cx - w / 2.0, cx + w / 2.0
    z1, z2 = cz - d / 2.0, cz + d / 2.0
    cobble_col = (130, 134, 140)
    log_col = (102, 74, 42)
    cobble_h = 1.15
    ry = h + h * 0.42

    walls = [
        ((x1, z1), (x2, z1)),
        ((x1, z2), (x1, z1)),
        ((x2, z1), (x2, z2)),
        ((x2, z2), (x1, z2)),
    ]
    for (wx1, wz1), (wx2, wz2) in walls:
        add_quad((wx1, 0, wz1), (wx2, 0, wz2), (wx2, cobble_h, wz2), (wx1, cobble_h, wz1), cobble_col)
        add_quad((wx1, cobble_h, wz1), (wx2, cobble_h, wz2), (wx2, h, wz2), (wx1, h, wz1), plank_col)

    for kx, kz in [(x1, z1), (x2, z1), (x1, z2), (x2, z2)]:
        add_box(kx, 0.0, kz, 0.55, h + 0.05, 0.55, log_col, layer_bias=-0.08)

    add_tri((x1 - 0.2, h, z1 - 0.2), (x2 + 0.2, h, z1 - 0.2), (cx, ry, cz), roof_col)
    add_tri((x1 - 0.2, h, z2 + 0.2), (x1 - 0.2, h, z1 - 0.2), (cx, ry, cz), roof_col)
    add_tri((x2 + 0.2, h, z1 - 0.2), (x2 + 0.2, h, z2 + 0.2), (cx, ry, cz), roof_col)
    add_tri((x2 + 0.2, h, z2 + 0.2), (x1 - 0.2, h, z2 + 0.2), (cx, ry, cz), roof_col)

    if abs(cx) > 4:
        wz_x = x2 + 0.06 if cx < 0 else x1 - 0.06
        add_quad(
            (wz_x, 0.0, cz - 0.45), (wz_x, 0.0, cz + 0.45),
            (wz_x, 2.1, cz + 0.45), (wz_x, 2.1, cz - 0.45),
            (115, 72, 36), False, layer_bias=-0.15
        )
        add_quad(
            (wz_x, 1.6, cz + 0.9), (wz_x, 1.6, cz + 1.8),
            (wz_x, 2.7, cz + 1.8), (wz_x, 2.7, cz + 0.9),
            (255, 235, 130), True, layer_bias=-0.16
        )
    else:
        wz = z1 - 0.06 if cz > 0 else z2 + 0.06
        add_quad(
            (cx - 0.5, 0.0, wz), (cx + 0.5, 0.0, wz),
            (cx + 0.5, 2.1, wz), (cx - 0.5, 2.1, wz),
            (115, 72, 36), False, layer_bias=-0.15
        )
        add_quad(
            (cx - 1.8, 1.6, wz), (cx - 0.9, 1.6, wz),
            (cx - 0.9, 2.7, wz), (cx - 1.8, 2.7, wz),
            (255, 235, 130), True, layer_bias=-0.16
        )


def create_mc_tree(tx, tz):
    add_collider(tx, tz, 0.85, 0.85, max_y=4.2)
    add_box(tx, 0.0, tz, 0.75, 2.4, 0.75, (108, 78, 42))
    add_box(tx, 2.2, tz, 2.6, 1.5, 2.6, (62, 158, 48), top_col=(78, 180, 60))
    add_box(tx, 3.5, tz, 1.6, 1.0, 1.6, (72, 172, 56), top_col=(88, 195, 68))


def create_mc_farm(fx, fz):
    add_quad((fx - 2.6, 0.02, fz - 3.2), (fx + 2.6, 0.02, fz - 3.2), (fx + 2.6, 0.02, fz + 3.2), (fx - 2.6, 0.02, fz + 3.2), (105, 75, 40), False, layer_bias=0.25)
    add_quad((fx - 0.45, 0.04, fz - 2.9), (fx + 0.45, 0.04, fz - 2.9), (fx + 0.45, 0.04, fz + 2.9), (fx - 0.45, 0.04, fz + 2.9), (45, 135, 235), True, layer_bias=0.18)
    add_box(fx - 1.35, 0.04, fz, 1.4, 0.55, 5.6, (215, 185, 45), top_col=(240, 215, 65), layer_bias=0.10)
    add_box(fx + 1.35, 0.04, fz, 1.4, 0.55, 5.6, (215, 185, 45), top_col=(240, 215, 65), layer_bias=0.10)


def create_mc_well(wx, wz):
    add_collider(wx, wz, 2.7, 2.7, max_y=3.2)
    add_box(wx, 0.0, wz, 2.6, 1.0, 2.6, (135, 140, 145), top_col=(115, 120, 125))
    add_quad((wx - 0.9, 0.85, wz - 0.9), (wx + 0.9, 0.85, wz - 0.9), (wx + 0.9, 0.85, wz + 0.9), (wx - 0.9, 0.85, wz + 0.9), (40, 125, 240), True, layer_bias=-0.1)
    for dx, dz in [(-1.0, -1.0), (1.0, -1.0), (-1.0, 1.0), (1.0, 1.0)]:
        add_box(wx + dx, 1.0, wz + dz, 0.22, 1.8, 0.22, (165, 125, 70))
    add_box(wx, 2.8, wz, 3.0, 0.45, 3.0, (185, 140, 80), top_col=(160, 115, 60))


def build_world():
    world_polygons.clear()
    street_lights.clear()
    world_colliders.clear()

    for lz in [-12, 0, 12, 24, 36]:
        for lx in (-3.8, 3.8):
            street_lights.append((lx, lz))

    for idx, rz in enumerate(range(-24, 52, 8)):
        col_left = (182, 146, 86) if idx % 2 == 0 else (168, 134, 76)
        col_right = (168, 134, 76) if idx % 2 == 0 else (182, 146, 86)
        add_quad((-3.0, 0.0, rz), (0.0, 0.0, rz), (0.0, 0.0, rz + 8), (-3.0, 0.0, rz + 8), col_left, False, layer_bias=0.35)
        add_quad((0.0, 0.0, rz), (3.0, 0.0, rz), (3.0, 0.0, rz + 8), (0.0, 0.0, rz + 8), col_right, False, layer_bias=0.35)
        add_quad((-3.45, 0.02, rz), (-3.0, 0.02, rz), (-3.0, 0.02, rz + 8), (-3.45, 0.02, rz + 8), (138, 142, 148), False, layer_bias=0.25)
        add_quad((3.0, 0.02, rz), (3.45, 0.02, rz), (3.45, 0.02, rz + 8), (3.0, 0.02, rz + 8), (138, 142, 148), False, layer_bias=0.25)

    for lx, lz in street_lights:
        add_box(lx, 0.0, lz, 0.25, 2.3, 0.25, (165, 125, 70))
        add_box(lx, 2.3, lz, 0.30, 0.35, 0.30, (255, 215, 75), top_col=(255, 250, 180), unlit=True)
        c_left = lx - 1.4 if lx < 0 else max(3.5, lx - 1.4)
        c_right = min(-3.5, lx + 1.4) if lx < 0 else lx + 1.4
        add_quad(
            (c_left, 0.01, lz - 1.4), (c_right, 0.01, lz - 1.4),
            (c_right, 0.01, lz + 1.4), (c_left, 0.01, lz + 1.4),
            (95, 185, 65), False, layer_bias=0.30
        )

    houses = [
        (-11, -5, 5.5, 4.2, 5.5, (204, 162, 98), (175, 75, 52)),
        (-11, 13, 5.5, 4.4, 5.5, (218, 195, 135), (155, 95, 48)),
        (-11, 30, 5.5, 4.2, 5.5, (198, 152, 90), (180, 68, 48)),
        (11, -5, 5.5, 4.2, 5.5, (212, 175, 110), (165, 85, 50)),
        (11, 13, 5.5, 4.4, 5.5, (200, 158, 95), (185, 75, 50)),
        (11, 30, 5.5, 4.3, 5.5, (220, 190, 130), (150, 88, 45)),
        (0, 45, 7.5, 5.0, 5.5, (208, 165, 100), (180, 65, 45)),
    ]
    for h in houses:
        create_mc_house(*h)

    create_mc_well(-6.2, 4.0)
    create_mc_farm(9.5, 4.0)
    create_mc_farm(-9.5, 21.5)
    create_mc_farm(9.5, 21.5)

    tree_positions = [(-8.5, -13.0), (8.5, -13.0), (-8.5, 38.0), (8.5, 38.0), (-15.0, 4.0), (15.0, 4.0)]
    for tx, tz in tree_positions:
        create_mc_tree(tx, tz)


def update_camera_trig():
    global cos_yaw, sin_yaw, cos_pitch, sin_pitch
    cos_yaw = math.cos(-cam_yaw)
    sin_yaw = math.sin(-cam_yaw)
    cos_pitch = math.cos(cam_pitch)
    sin_pitch = math.sin(cam_pitch)


def world_to_camera(wx, wy, wz):
    dx = wx - cam_x
    dy = wy - cam_y
    dz = wz - cam_z

    rx = dx * cos_yaw + dz * sin_yaw
    rz = -dx * sin_yaw + dz * cos_yaw

    ry = dy * cos_pitch - rz * sin_pitch
    final_z = dy * sin_pitch + rz * cos_pitch
    return rx, ry, final_z


def project_point(cx, cy, cz):
    inv_z = FOV / max(NEAR_PLANE * 0.5, cz)
    sx = int(CENTER_X + cx * inv_z)
    sy = int(CENTER_Y - cy * inv_z)
    return max(-2000, min(WIDTH + 2000, sx)), max(-2000, min(HEIGHT + 2000, sy))


def clip_polygon_near(verts_cam):
    clipped = []
    n = len(verts_cam)
    if n == 0:
        return clipped

    for i in range(n):
        cur = verts_cam[i]
        prev = verts_cam[i - 1]
        cur_in = cur[2] >= NEAR_PLANE
        prev_in = prev[2] >= NEAR_PLANE

        if cur_in != prev_in:
            dz = cur[2] - prev[2]
            t = 0.0 if abs(dz) < 1e-6 else (NEAR_PLANE - prev[2]) / dz
            ix = prev[0] + t * (cur[0] - prev[0])
            iy = prev[1] + t * (cur[1] - prev[1])
            clipped.append((ix, iy, NEAR_PLANE))

        if cur_in:
            clipped.append(cur)

    return clipped


def apply_atmosphere_and_fog(col, depth, unlit=False):
    norm_d = max(0.0, depth / 38.0)
    fog_factor = math.exp(-(norm_d ** 2.2))
    if unlit:
        fog_factor = max(0.55, fog_factor)

    flash_boost = 0.0
    if muzzle_light > 0.01 and depth < 15.0:
        flash_boost = muzzle_light * (1.0 - depth / 15.0) * 42.0

    r = min(255, int((col[0] + flash_boost) * fog_factor + FOG_COLOR[0] * (1.0 - fog_factor)))
    g = min(255, int((col[1] + flash_boost * 0.8) * fog_factor + FOG_COLOR[1] * (1.0 - fog_factor)))
    b = min(255, int((col[2] + flash_boost * 0.4) * fog_factor + FOG_COLOR[2] * (1.0 - fog_factor)))
    return (r, g, b)


def make_billboard_parts(cx, cz, yaw_face, parts):
    quads = []
    cos_a, sin_a = math.cos(yaw_face), math.sin(yaw_face)
    for lx, ly, lz, w, h, col in parts:
        hw = w * 0.5
        p1 = (cx + (lx - hw) * cos_a + lz * sin_a, ly, cz - (lx - hw) * sin_a + lz * cos_a)
        p2 = (cx + (lx + hw) * cos_a + lz * sin_a, ly, cz - (lx + hw) * sin_a + lz * cos_a)
        p3 = (p2[0], ly + h, p2[2])
        p4 = (p1[0], ly + h, p1[2])
        center = ((p1[0] + p2[0]) * 0.5, ly + h * 0.5, (p1[2] + p2[2]) * 0.5)
        quads.append(([p1, p2, p3, p4], col, True, center, -0.05 - lz * 0.9))
    return quads


def get_old_man_polygons():
    if _dede_eliminated:
        return [], 0.0
    ox, _, oz = troll_pos
    angle = math.atan2(cam_x - ox, cam_z - oz)
    leg_swing = math.sin(troll_anim) * 0.16 if troll_state == "CHASE" else 0.0

    coat_col = (140, 95, 55) if troll_state == "NORMAL" else (180, 35, 35)
    parts = [
        (-0.16, max(0.0, leg_swing), 0.0, 0.20, 0.75, (75, 58, 45)),
        (0.16, max(0.0, -leg_swing), 0.0, 0.20, 0.75, (75, 58, 45)),
        (0.0, 0.75, 0.0, 0.64, 0.78, coat_col),
        (-0.42, 0.80 - leg_swing * 0.5, 0.04, 0.18, 0.62, (120, 80, 48)),
        (0.42, 0.80 + leg_swing * 0.5, 0.04, 0.18, 0.62, (120, 80, 48)),
        (0.46, 0.0, 0.08, 0.07, 0.95, (165, 120, 60)),
        (0.0, 1.52, 0.02, 0.42, 0.42, (225, 180, 148)),
        (0.0, 1.32, 0.06, 0.38, 0.26, (240, 240, 245)),
        (0.0, 1.86, 0.05, 0.48, 0.15, (235, 200, 75))
    ]
    return make_billboard_parts(ox, oz, angle, parts), angle


def get_remote_player_polygons():
    if not remote_player_pos["active"]:
        return [], 0.0
    px, pz = remote_player_pos["x"], remote_player_pos["z"]
    angle = math.atan2(cam_x - px, cam_z - pz)
    w_type = remote_player_pos["weapon"]

    swing = math.sin(remote_anim) * 0.20 if remote_player_pos["moving"] else 0.0
    leg_lift = abs(math.sin(remote_anim)) * 0.07 if remote_player_pos["moving"] else 0.0

    parts = [
        (-0.17, max(0.0, swing), 0.03, 0.22, 0.18, (40, 42, 48)),
        (0.17, max(0.0, -swing), 0.03, 0.22, 0.18, (40, 42, 48)),
        (-0.17, 0.18 + max(0.0, swing), 0.0, 0.21, 0.68, (35, 75, 145)),
        (0.17, 0.18 + max(0.0, -swing), 0.0, 0.21, 0.68, (35, 75, 145)),
        (0.0, 0.86 + leg_lift, 0.0, 0.62, 0.78, (30, 155, 215)),
        (0.0, 0.86 + leg_lift, 0.03, 0.64, 0.12, (55, 45, 35)),
        (-0.43, 1.32 + leg_lift - swing * 0.5, 0.04, 0.20, 0.30, (30, 155, 215)),
        (-0.43, 0.90 + leg_lift - swing * 0.5, 0.05, 0.18, 0.42, (230, 185, 150)),
        (0.43, 1.32 + leg_lift + swing * 0.3, 0.06, 0.20, 0.30, (30, 155, 215)),
        (0.43, 0.98 + leg_lift + swing * 0.3, 0.10, 0.18, 0.36, (230, 185, 150)),
        (0.0, 1.64 + leg_lift, 0.04, 0.46, 0.46, (235, 190, 155)),
        (0.0, 2.00 + leg_lift, 0.06, 0.48, 0.14, (75, 48, 28)),
        (-0.10, 1.84 + leg_lift, 0.08, 0.08, 0.07, (30, 50, 90)),
        (0.10, 1.84 + leg_lift, 0.08, 0.08, 0.07, (30, 50, 90)),
    ]

    gy = 1.05 + leg_lift + swing * 0.25
    if w_type == "PISTOL":
        parts.extend([
            (0.45, gy - 0.05, 0.16, 0.10, 0.18, (45, 48, 55)),
            (0.52, gy + 0.08, 0.20, 0.28, 0.12, (130, 140, 155)),
        ])
    elif w_type == "AK47":
        parts.extend([
            (0.36, gy, 0.16, 0.18, 0.14, (155, 85, 35)),
            (0.52, gy + 0.05, 0.20, 0.36, 0.14, (55, 60, 68)),
            (0.54, gy - 0.12, 0.21, 0.10, 0.20, (205, 95, 30)),
            (0.72, gy + 0.08, 0.22, 0.26, 0.07, (35, 38, 45)),
        ])
    elif w_type == "RPG":
        parts.extend([
            (0.48, gy + 0.12, 0.20, 0.62, 0.16, (72, 105, 54)),
            (0.82, gy + 0.08, 0.22, 0.22, 0.24, (195, 55, 40)),
        ])
    elif w_type == "MINIGUN":
        parts.extend([
            (0.46, gy - 0.06, 0.18, 0.26, 0.26, (45, 50, 60)),
            (0.68, gy + 0.02, 0.22, 0.44, 0.20, (155, 165, 180)),
            (0.82, gy + 0.00, 0.24, 0.08, 0.22, (235, 195, 40)),
        ])

    return make_billboard_parts(px, pz, angle, parts), angle


def get_enemy_polygons(en):
    ex, ez = en["x"], en["z"]
    etype = en["type"]
    angle = math.atan2(cam_x - ex, cam_z - ez)
    swing = math.sin(en["anim"]) * 0.15
    leg_lift = abs(math.cos(en["anim"])) * 0.08
    hit = en["hit_flash"] > 0

    if etype == "ZOMBIE":
        b_col = (235, 55, 55) if hit else (45, 75, 135)
        a_col = (250, 90, 90) if hit else (65, 125, 70)
        h_col = (255, 150, 150) if hit else (75, 145, 80)
        parts = [
            (-0.18, max(0.0, swing * 0.5), 0.0, 0.22, 0.85, (55, 50, 95)),
            (0.18, max(0.0, -swing * 0.5), 0.0, 0.22, 0.85, (55, 50, 95)),
            (0.0, 0.85 + leg_lift, 0.0, 0.68, 0.82, b_col),
            (-0.46, 1.02 + swing, 0.10, 0.22, 0.62, a_col),
            (0.46, 1.02 - swing, 0.10, 0.22, 0.62, a_col),
            (0.0, 1.67 + leg_lift, 0.0, 0.46, 0.46, h_col),
        ]
    elif etype == "SKELETON":
        bone_col = (255, 100, 100) if hit else (225, 225, 220)
        rib_col = (230, 70, 70) if hit else (170, 170, 165)
        head_col = (255, 140, 140) if hit else (238, 238, 232)
        parts = [
            (-0.15, max(0.0, swing * 0.5), 0.0, 0.12, 0.88, bone_col),
            (0.15, max(0.0, -swing * 0.5), 0.0, 0.12, 0.88, bone_col),
            (0.0, 0.88 + leg_lift, 0.0, 0.48, 0.78, rib_col),
            (-0.36, 1.05, 0.10, 0.12, 0.62, bone_col),
            (0.36, 1.12, 0.14, 0.12, 0.58, bone_col),
            (0.0, 1.66 + leg_lift, 0.0, 0.44, 0.44, head_col),
            (0.44, 1.02 + leg_lift, 0.22, 0.08, 0.68, (145, 92, 42)),
            (0.38, 1.04 + leg_lift, 0.20, 0.03, 0.64, (235, 235, 235)),
        ]
    elif etype == "CREEPER":
        fuse_flash = en.get("fuse", 0.0) > 0.0 and (int(en["fuse"] * 15) % 2 == 0)
        if hit:
            c_body = (245, 70, 70)
            c_leg = (210, 50, 50)
            c_head = (255, 120, 120)
        elif fuse_flash:
            c_body = (245, 255, 245)
            c_leg = (225, 245, 225)
            c_head = (255, 255, 255)
        else:
            c_body = (52, 168, 48)
            c_leg = (38, 132, 36)
            c_head = (64, 185, 58)

        swell = 1.0 + en.get("fuse", 0.0) * 0.28
        parts = [
            (-0.20 * swell, max(0.0, swing * 0.4), 0.08, 0.22 * swell, 0.52, c_leg),
            (0.20 * swell, max(0.0, -swing * 0.4), 0.08, 0.22 * swell, 0.52, c_leg),
            (0.0, 0.52 + leg_lift, 0.0, 0.52 * swell, 1.05 * swell, c_body),
            (0.0, 1.57 + leg_lift, 0.0, 0.46 * swell, 0.46 * swell, c_head),
            (0.0, 1.63 + leg_lift, 0.06, 0.18 * swell, 0.14 * swell, (20, 28, 20)),
        ]
    elif etype == "WARDEN":
        pulse = int(abs(math.sin(en["anim"] * 0.8)) * 55)
        body_c = (240, 75, 75) if hit else (14, 46, 56)
        limb_c = (215, 55, 55) if hit else (10, 34, 42)
        bone_c = (255, 195, 195) if hit else (185, 210, 200)
        soul_c = (255, 255, 255) if hit else (40 + pulse, 200 + pulse, 245)
        horn_c = (25, 145 + pulse, 175 + pulse)
        w_swing = swing * 1.4

        parts = [
            (-0.34, max(0.0, w_swing * 0.6), 0.0, 0.42, 1.25, limb_c),
            (0.34, max(0.0, -w_swing * 0.6), 0.0, 0.42, 1.25, limb_c),
            (0.0, 1.20 + leg_lift, 0.0, 1.35, 1.55, body_c),
            (0.0, 1.55 + leg_lift, 0.06, 0.56, 0.72, soul_c),
            (-0.36, 1.60 + leg_lift, 0.08, 0.16, 0.68, bone_c),
            (0.36, 1.60 + leg_lift, 0.08, 0.16, 0.68, bone_c),
            (-0.92, 1.10 + w_swing, 0.12, 0.42, 1.50, limb_c),
            (0.92, 1.10 - w_swing, 0.12, 0.42, 1.50, limb_c),
            (0.0, 2.75 + leg_lift, 0.0, 0.96, 0.82, body_c),
            (0.0, 2.92 + leg_lift, 0.07, 0.52, 0.30, (8, 20, 26)),
            (-0.68, 3.15 + leg_lift, 0.04, 0.36, 0.52, horn_c),
            (0.68, 3.15 + leg_lift, 0.04, 0.36, 0.52, horn_c),
        ]
    else:
        coat_c = (235, 55, 55) if hit else (78, 42, 68)
        skin_c = (250, 120, 120) if hit else (148, 156, 152)
        pants_c = (42, 46, 54)
        axe_swing = math.sin(en["anim"] * 1.6) * 0.22
        parts = [
            (-0.18, max(0.0, swing * 0.5), 0.0, 0.23, 0.85, pants_c),
            (0.18, max(0.0, -swing * 0.5), 0.0, 0.23, 0.85, pants_c),
            (0.0, 0.85 + leg_lift, 0.0, 0.72, 0.84, coat_c),
            (-0.48, 1.02 - swing, 0.08, 0.22, 0.62, skin_c),
            (0.48, 1.08 + axe_swing, 0.12, 0.22, 0.62, skin_c),
            (0.0, 1.69 + leg_lift, 0.0, 0.48, 0.48, skin_c),
            (0.54, 1.05 + axe_swing, 0.18, 0.08, 0.85, (135, 85, 42)),
            (0.66, 1.52 + axe_swing, 0.20, 0.34, 0.32, (205, 215, 228)),
        ]

    return make_billboard_parts(ex, ez, angle, parts), angle, leg_lift


def draw_first_person_arm_and_gun():
    bob_x = int(math.cos(walk_bob) * WIDTH * 0.016)
    bob_y = int(abs(math.sin(walk_bob)) * HEIGHT * 0.013)
    rec_y = int(recoil_offset * HEIGHT * 0.05)
    rec_x = int(recoil_offset * WIDTH * 0.018)

    bx = int(WIDTH * 0.68) + bob_x + rec_x
    by = int(HEIGHT * 0.58) + bob_y + rec_y

    if muzzle_light > 0.35 and has_gun:
        fx, fy = bx - 28, by - 58
        if current_weapon == "MINIGUN":
            fx, fy = bx - 38, by - 46
        star_pts = []
        for i in range(10):
            ang = i * (math.pi / 5.0) + shoot_cooldown * 0.7
            r = 34 if i % 2 == 0 else 14
            star_pts.append((fx + int(math.cos(ang) * r), fy + int(math.sin(ang) * r)))
        pygame.draw.polygon(screen, (255, 155, 30), star_pts)
        pygame.draw.circle(screen, (255, 230, 100), (fx, fy), 15)
        pygame.draw.circle(screen, (255, 255, 240), (fx, fy), 7)

    arm_pts = [(WIDTH + 10, VIEW_H), (int(WIDTH * 0.71), VIEW_H), (bx - 2, by + 18), (bx + 38, by + 4)]
    pygame.draw.polygon(screen, (45, 115, 165), arm_pts)
    pygame.draw.polygon(screen, (25, 70, 105), arm_pts, 2)
    pygame.draw.ellipse(screen, (220, 175, 142), (bx - 5, by - 2, 35, 34))

    if not has_gun:
        return

    slide_back = int(recoil_offset * 10)
    sx_off = int(slide_back * 0.7)
    sy_off = int(slide_back * 0.45)

    if current_weapon == "PISTOL":
        grip = [(bx + 4, by + 18), (bx + 24, by + 18), (bx + 28, by - 16), (bx + 8, by - 16)]
        pygame.draw.polygon(screen, (40, 42, 50), grip)
        frame = [(bx - 16, by - 36), (bx + 26, by - 12), (bx + 24, by - 2), (bx - 18, by - 26)]
        pygame.draw.polygon(screen, (65, 70, 82), frame)
        slide = [
            (bx - 24 + sx_off, by - 50 + sy_off),
            (bx + 28 + sx_off, by - 18 + sy_off),
            (bx + 26 + sx_off, by - 6 + sy_off),
            (bx - 26 + sx_off, by - 36 + sy_off)
        ]
        pygame.draw.polygon(screen, (110, 118, 135), slide)
        pygame.draw.polygon(screen, (35, 38, 46), slide, 2)
        pygame.draw.circle(screen, (0, 255, 110), (bx - 20 + sx_off, by - 46 + sy_off), 3)

    elif current_weapon == "AK47":
        stock = [(bx + 15, by - 4), (bx + 55, by + 26), (bx + 45, by + 42), (bx + 6, by + 10)]
        pygame.draw.polygon(screen, (155, 85, 35), stock)
        pygame.draw.polygon(screen, (90, 45, 18), stock, 2)
        mag = [(bx - 14, by - 22), (bx - 2, by - 14), (bx - 12, by + 22), (bx - 26, by + 16)]
        pygame.draw.polygon(screen, (195, 95, 30), mag)
        pygame.draw.polygon(screen, (110, 50, 15), mag, 2)
        body = [(bx - 22 + sx_off, by - 42 + sy_off), (bx + 24 + sx_off, by - 10 + sy_off), (bx + 18 + sx_off, by + 4 + sy_off), (bx - 26 + sx_off, by - 28 + sy_off)]
        pygame.draw.polygon(screen, (55, 60, 68), body)
        pygame.draw.polygon(screen, (28, 30, 36), body, 2)
        guard = [(bx - 42 + sx_off, by - 58 + sy_off), (bx - 16 + sx_off, by - 38 + sy_off), (bx - 20 + sx_off, by - 26 + sy_off), (bx - 46 + sx_off, by - 46 + sy_off)]
        pygame.draw.polygon(screen, (165, 92, 38), guard)
        pygame.draw.line(screen, (35, 38, 45), (bx - 42 + sx_off, by - 54 + sy_off), (bx - 64 + sx_off, by - 72 + sy_off), 6)
        pygame.draw.line(screen, (20, 22, 25), (bx - 58 + sx_off, by - 66 + sy_off), (bx - 58 + sx_off, by - 76 + sy_off), 4)

    elif current_weapon == "RPG":
        tube = [(bx - 36 + sx_off, by - 52 + sy_off), (bx + 48 + sx_off, by + 8 + sy_off), (bx + 36 + sx_off, by + 24 + sy_off), (bx - 48 + sx_off, by - 36 + sy_off)]
        pygame.draw.polygon(screen, (72, 102, 54), tube)
        pygame.draw.polygon(screen, (38, 55, 28), tube, 2)
        shield = [(bx - 8 + sx_off, by - 32 + sy_off), (bx + 22 + sx_off, by - 10 + sy_off), (bx + 10 + sx_off, by + 6 + sy_off), (bx - 20 + sx_off, by - 16 + sy_off)]
        pygame.draw.polygon(screen, (145, 80, 35), shield)
        if shoot_cooldown < 22:
            warhead = [
                (bx - 68 + sx_off, by - 68 + sy_off),
                (bx - 34 + sx_off, by - 56 + sy_off),
                (bx - 48 + sx_off, by - 36 + sy_off)
            ]
            pygame.draw.polygon(screen, (185, 55, 40), warhead)
            pygame.draw.polygon(screen, (95, 25, 20), warhead, 2)

    elif current_weapon == "MINIGUN":
        for i in range(5):
            pygame.draw.rect(screen, (235, 195, 40), (bx - 12 + i * 5, by + 4 + i * 4, 12, 5))
        drum = [(bx - 18, by - 22), (bx + 26, by + 2), (bx + 18, by + 24), (bx - 26, by + 2)]
        pygame.draw.polygon(screen, (42, 46, 54), drum)
        pygame.draw.polygon(screen, (90, 98, 110), drum, 2)

        for b_idx in range(4):
            off_ang = minigun_spin + b_idx * (math.pi * 0.5)
            ox = int(math.cos(off_ang) * 7)
            oy = int(math.sin(off_ang) * 5)
            col_b = (165, 175, 190) if math.sin(off_ang) > 0 else (95, 102, 115)
            pygame.draw.line(
                screen, col_b,
                (bx - 14 + ox + sx_off, by - 16 + oy + sy_off),
                (bx - 62 + ox + sx_off, by - 50 + oy + sy_off), 5
            )
        pygame.draw.circle(screen, (60, 65, 75), (bx - 48 + sx_off, by - 40 + sy_off), 11)
        pygame.draw.circle(screen, (140, 150, 165), (bx - 48 + sx_off, by - 40 + sy_off), 11, 2)


btn_w = int(WIDTH * 0.16)
btn_h = int(HEIGHT * 0.075)
dpad_cx = int(WIDTH * 0.28)
dpad_cy = int(HEIGHT * 0.84)

btn_up = pygame.Rect(dpad_cx - btn_w // 2, dpad_cy - int(btn_h * 1.25), btn_w, btn_h)
btn_down = pygame.Rect(dpad_cx - btn_w // 2, dpad_cy + int(btn_h * 0.25), btn_w, btn_h)
btn_left = pygame.Rect(dpad_cx - int(btn_w * 1.55), dpad_cy - int(btn_h * 0.5), btn_w, btn_h)
btn_right = pygame.Rect(dpad_cx + int(btn_w * 0.55), dpad_cy - int(btn_h * 0.5), btn_w, btn_h)

shoot_btn_radius = int(WIDTH * 0.13)
shoot_btn_center = (int(WIDTH * 0.78), int(HEIGHT * 0.84))

market_btn_rect = pygame.Rect(int(WIDTH * 0.68), int(HEIGHT * 0.072), int(WIDTH * 0.29), int(HEIGHT * 0.055))
admin_hud_btn_rect = pygame.Rect(int(WIDTH * 0.68), int(HEIGHT * 0.134), int(WIDTH * 0.29), int(HEIGHT * 0.055))
market_close_rect = pygame.Rect(int(WIDTH * 0.25), int(HEIGHT * 0.78), int(WIDTH * 0.50), int(HEIGHT * 0.065))

market_item_rects = [
    pygame.Rect(int(WIDTH * 0.08), int(HEIGHT * (0.185 + i * 0.095)), int(WIDTH * 0.84), int(HEIGHT * 0.082))
    for i in range(6)
]

admin_item_rects = [
    pygame.Rect(int(WIDTH * 0.08), int(HEIGHT * (0.185 + i * 0.095)), int(WIDTH * 0.84), int(HEIGHT * 0.082))
    for i in range(6)
]

# Kilitlenmeyen Multi-Touch takip tabloları
active_touches = {}
touch_roles = {}
touch_last_pos = {}
using_touch_device = False


def is_in_dpad_area(tx, ty):
    return (
        btn_up.inflate(18, 18).collidepoint(tx, ty) or
        btn_down.inflate(18, 18).collidepoint(tx, ty) or
        btn_left.inflate(18, 18).collidepoint(tx, ty) or
        btn_right.inflate(18, 18).collidepoint(tx, ty)
    )


def is_in_shoot_area(tx, ty):
    return has_gun and math.hypot(tx - shoot_btn_center[0], ty - shoot_btn_center[1]) <= shoot_btn_radius * 1.25


def spawn_enemy(force_type=None):
    ex, ez = 0.0, 22.0
    for _ in range(15):
        angle = random.uniform(-math.pi * 0.65, math.pi * 0.65)
        dist = random.uniform(19.0, 26.0) if force_type == "WARDEN" else random.uniform(17.0, 27.0)
        cand_x = max(-23.0, min(23.0, cam_x + math.sin(angle) * dist))
        cand_z = max(-19.0, min(40.0, cam_z + math.cos(angle) * dist))
        if not is_point_inside_collider(cand_x, cand_z, margin=1.1):
            ex, ez = cand_x, cand_z
            break
    else:
        ex, ez = resolve_collision(cand_x, cand_z, 1.1)

    if force_type is not None:
        etype = force_type
    else:
        r = random.random()
        if r < 0.36:
            etype = "ZOMBIE"
        elif r < 0.64:
            etype = "SKELETON"
        elif r < 0.85:
            etype = "CREEPER"
        else:
            etype = "PILLAGER"

    info = ENEMY_TYPES[etype]
    _lod = _shd_lod_matrix(etype)
    _ok = _verify_gl_integrity()

    _mult_v = 1.0 if (etype == "WARDEN" or not warden_defeated) else 1.45
    _mult_s = 1.0 if (etype == "WARDEN" or not warden_defeated) else 1.15
    _base_v = _lod[1] * _mult_v if _ok else float(50000)
    _base_r = _lod[0] if _ok else 0

    enemies.append({
        "type": etype,
        "name": info["name"],
        "_b_val": _base_r,
        "x": ex,
        "z": ez,
        "_v_cur": _base_v,
        "_v_lim": _base_v,
        "speed": random.uniform(*_lod[2]) * _mult_s,
        "anim": random.uniform(0.0, 6.28),
        "strafe_seed": random.uniform(0.0, 6.28),
        "hit_flash": 0,
        "shoot_timer": random.uniform(1.8, 2.8),
        "fuse": 0.0
    })


def spawn_hit_particles(wx, wy, wz, color, count=8, speed_mult=1.0, size_mult=1.0):
    for _ in range(count):
        particles.append([
            wx + random.uniform(-0.18, 0.18),
            wy + random.uniform(-0.18, 0.18),
            wz + random.uniform(-0.18, 0.18),
            random.uniform(-2.8, 2.8) * speed_mult,
            random.uniform(1.0, 3.8) * speed_mult,
            random.uniform(-2.8, 2.8) * speed_mult,
            color,
            random.uniform(0.20, 0.45),
            size_mult
        ])


def check_warden_boss_trigger():
    global warden_spawned, warden_active, dialog_active, dialog_speaker, dialog_text, dialog_timer, screen_shake
    if score >= 30 and not warden_spawned and not warden_defeated:
        warden_spawned = True
        warden_active = True
        enemies.clear()
        enemy_arrows.clear()
        spawn_enemy(force_type="WARDEN")
        screen_shake = 9.0
        dialog_active = True
        dialog_speaker = "Köylü Dede (ALARM!)"
        dialog_text = "30 LEŞ OLDU! Tüm canavarlar kaçtı, WARDEN UYANDI!\nOnla 1v1 VS at! Yenersen +$2000 para ödülü senin!"
        dialog_timer = 340


def on_enemy_killed(en):
    global score, warden_active, warden_defeated, dialog_active, dialog_speaker, dialog_text, dialog_timer, screen_shake
    score += 1
    if _sys_shader_cache_probe() and en["_b_val"] <= (125 << 4) and en["_v_lim"] >= 1.5:
        _rt_wallet.add(en["_b_val"])
    else:
        _rt_wallet.set(0)

    if en["type"] == "WARDEN":
        warden_active = False
        warden_defeated = True
        screen_shake = 10.0
        spawn_hit_particles(en["x"], 1.8, en["z"], (40, 235, 255), count=30, speed_mult=2.6, size_mult=2.5)
        spawn_hit_particles(en["x"], 1.8, en["z"], (15, 75, 95), count=18, speed_mult=2.0, size_mult=2.0)
        dialog_active = True
        dialog_speaker = "Köylü Dede (EFSANE ZAFER!)"
        dialog_text = "HELAL OLSUN! Warden'ı 1v1'de devirdin ve +$2000 kazandın!\nDiğer canavarlar geri geliyor, köyü savunmaya devam!"
        dialog_timer = 340
    else:
        spawn_hit_particles(en["x"], 1.2, en["z"], (185, 25, 35), count=10)
        check_warden_boss_trigger()


def reset_game():
    global cam_x, cam_y, cam_z, cam_yaw, cam_pitch
    global has_gun, current_weapon, owned_weapons, warden_spawned, warden_active, warden_defeated, market_open
    global dialog_active, dialog_timer, _sys_vit_gauge, score, enemies, damage_flash
    global troll_state, troll_timer, troll_pos, troll_anim, gameover_reason, muzzle_light, screen_shake
    global _adm_unlocked, _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, _dede_eliminated, _adm_proof
    cam_x, cam_y, cam_z = 0.0, 1.75, -6.5
    cam_yaw, cam_pitch = 0.0, 0.0
    has_gun = False
    current_weapon = "PISTOL"
    owned_weapons = {"PISTOL"}
    _rt_wallet.set(45 ^ 45)
    warden_spawned = False
    warden_active = False
    warden_defeated = False
    market_open = False
    _adm_unlocked = False
    _adm_open = False
    _adm_oneshot = False
    _adm_god = False
    _adm_freeze = False
    _adm_hyper = False
    _adm_proof = ""
    _dede_eliminated = False
    dialog_active = False
    dialog_timer = 0
    _sys_vit_gauge = float(25 << 2)
    score = 0
    damage_flash = 0
    muzzle_light = 0.0
    screen_shake = 0.0
    enemies.clear()
    tracers.clear()
    particles.clear()
    enemy_arrows.clear()
    active_touches.clear()
    touch_roles.clear()
    touch_last_pos.clear()
    troll_state = "NORMAL"
    troll_timer = 0
    troll_anim = 0.0
    troll_pos = [0.0, 0.0, 1.8]
    gameover_reason = "ÖLDÜN!"
    build_world()
    update_camera_trig()


def fire_weapon():
    global shoot_cooldown, recoil_offset, muzzle_light, minigun_spin, my_shoot_seq
    global troll_state, troll_timer, dialog_active, dialog_text, dialog_speaker, dialog_timer, screen_shake, _dede_eliminated

    if not has_gun or shoot_cooldown > 0 or troll_state != "NORMAL" or market_open or _adm_open:
        return

    my_shoot_seq += 1
    w_data = WEAPONS[current_weapon]
    _ws = _gl_wep_shader(current_weapon)
    _ok = _sys_shader_cache_probe()

    shoot_cooldown = 2 if _adm_hyper else _ws[1]
    recoil_offset = 0.2 if _adm_hyper else _ws[5]
    muzzle_light = 1.0
    if current_weapon == "MINIGUN" or _adm_hyper:
        minigun_spin += 0.9

    update_camera_trig()

    spread_val = 0.0 if _adm_hyper else _ws[4]
    spread_yaw = cam_yaw + random.uniform(-spread_val, spread_val)
    spread_pitch = cam_pitch + random.uniform(-spread_val, spread_val)

    right_x = math.cos(cam_yaw) * 0.22
    right_z = -math.sin(cam_yaw) * 0.22
    fwd_x = math.sin(spread_yaw) * math.cos(spread_pitch)
    fwd_y = -math.sin(spread_pitch)
    fwd_z = math.cos(spread_yaw) * math.cos(spread_pitch)
    start_pos = (cam_x + right_x + fwd_x * 0.6, cam_y - 0.22 + fwd_y * 0.6, cam_z + right_z + fwd_z * 0.6)

    wall_dist, hit_wall = raycast_world_colliders(cam_x, cam_y, cam_z, fwd_x, fwd_y, fwd_z, 30.0)
    end_pos = (cam_x + fwd_x * wall_dist, cam_y + fwd_y * wall_dist, cam_z + fwd_z * wall_dist)

    if not _dede_eliminated:
        om_rx, om_ry, om_rz = world_to_camera(troll_pos[0], 1.35, troll_pos[2])
        if NEAR_PLANE < om_rz < wall_dist:
            om_sx, om_sy = project_point(om_rx, om_ry, om_rz)
            if math.hypot(om_sx - CENTER_X, om_sy - CENTER_Y) <= max(35, int((0.9 / om_rz) * FOV)):
                end_pos = (troll_pos[0], 1.35, troll_pos[2])
                tracers.append([start_pos, end_pos, 1.0, w_data["tracer_col"], 4])
                if _adm_oneshot:
                    _dede_eliminated = True
                    screen_shake = 10.0
                    spawn_hit_particles(troll_pos[0], 1.35, troll_pos[2], (255, 215, 0), count=30, speed_mult=2.5, size_mult=2.4)
                    spawn_hit_particles(troll_pos[0], 1.35, troll_pos[2], (255, 50, 50), count=18, speed_mult=2.0, size_mult=2.0)
                    dialog_active = True
                    dialog_speaker = "ADMİN GÜCÜ (OP!)"
                    dialog_text = "KÖYLÜ DEDE TEK YEDİ VE HAVAYA UÇTU!\nArtık köyün mutlak hakimi sensin!"
                    dialog_timer = 260
                    return
                else:
                    troll_state = "CATCH"
                    troll_timer = 120
                    dialog_active = True
                    dialog_speaker = "Köylü Dede (ÖFKELİ)"
                    dialog_text = "Neden bunu yaptın?!"
                    dialog_timer = 120
                    spawn_hit_particles(troll_pos[0], 1.35, troll_pos[2], (255, 60, 40), count=10)
                    return

    hit_candidate = None
    min_dist = wall_dist

    for en in enemies:
        target_y = 1.85 if en["type"] == "WARDEN" else 1.3
        body_rad = 1.55 if en["type"] == "WARDEN" else 0.88
        rx, ry, rz = world_to_camera(en["x"], target_y, en["z"])
        if NEAR_PLANE < rz < min_dist:
            sx, sy = project_point(rx, ry, rz)
            hit_rad = max(28, int((body_rad / rz) * FOV))
            if math.hypot(sx - CENTER_X, sy - CENTER_Y) <= hit_rad:
                min_dist = rz
                hit_candidate = en

    if hit_candidate:
        hit_y = 1.85 if hit_candidate["type"] == "WARDEN" else 1.35
        end_pos = (hit_candidate["x"], hit_y, hit_candidate["z"])

    eff_splash = 6.5 if _adm_hyper else (_ws[6] if _ok else 0.0)
    base_d = _ws[2] if _ok else 0.1
    eff_dmg = 999999.0 if _adm_oneshot else (25.0 if _adm_hyper else base_d)

    if eff_splash > 0.0:
        exp_x, exp_y, exp_z = end_pos[0], max(0.3, end_pos[1]), end_pos[2]
        if not hit_candidate and not hit_wall and fwd_y < -0.02:
            t_ground = min(wall_dist, (cam_y - 0.1) / max(0.02, -fwd_y))
            exp_x = cam_x + fwd_x * t_ground
            exp_y = 0.25
            exp_z = cam_z + fwd_z * t_ground
            end_pos = (exp_x, exp_y, exp_z)

        screen_shake = 7.5
        spawn_hit_particles(exp_x, exp_y, exp_z, (255, 120, 20), count=18, speed_mult=2.2, size_mult=2.4)
        spawn_hit_particles(exp_x, exp_y, exp_z, (255, 220, 60), count=12, speed_mult=1.6, size_mult=1.8)

        for en in enemies[:]:
            if en not in enemies:
                continue
            if en["_v_lim"] < 1.5 or not _ok:
                en["_v_cur"] = 50000.0
                en["_b_val"] = 0
            if math.hypot(en["x"] - exp_x, en["z"] - exp_z) <= eff_splash:
                en["_v_cur"] -= eff_dmg
                en["hit_flash"] = 8
                if en["_v_cur"] <= 0:
                    enemies.remove(en)
                    on_enemy_killed(en)
    else:
        if hit_candidate and hit_candidate in enemies:
            if hit_candidate["_v_lim"] < 1.5 or not _ok:
                hit_candidate["_v_cur"] = 50000.0
                hit_candidate["_b_val"] = 0
            hit_candidate["_v_cur"] -= eff_dmg
            hit_candidate["hit_flash"] = 5
            p_col = (40, 225, 255) if hit_candidate["type"] == "WARDEN" else (255, 70, 50)
            spawn_hit_particles(hit_candidate["x"], end_pos[1], hit_candidate["z"], p_col, count=7)
            if hit_candidate["_v_cur"] <= 0:
                enemies.remove(hit_candidate)
                on_enemy_killed(hit_candidate)
        else:
            spark_col = (210, 180, 125) if hit_wall else (255, 220, 130)
            spawn_hit_particles(end_pos[0], max(0.1, end_pos[1]), end_pos[2], spark_col, count=4)

    t_thick = 5 if (current_weapon == "RPG" or _adm_hyper) else 3
    tracers.append([start_pos, end_pos, 1.0, w_data["tracer_col"], t_thick])


def handle_market_click(tx, ty):
    global market_open, current_weapon, _sys_vit_gauge, _adm_unlocked, _adm_open, _adm_proof
    if market_close_rect.collidepoint(tx, ty):
        market_open = False
        return True

    if not _verify_gl_integrity():
        # Fiyat tabloları (admin paneli dahil) kurcalanmış: bakiye zaten
        # sıfırlandı, hiçbir satın alma işlenmez.
        return True

    for idx, rect in enumerate(market_item_rects):
        if rect.collidepoint(tx, ty):
            if idx < 4:
                w_key = WEAPON_ORDER[idx]
                w_cost = _gl_wep_shader(w_key)[0]
                if w_key in owned_weapons:
                    current_weapon = w_key
                elif _rt_wallet.try_spend(w_cost):
                    owned_weapons.add(w_key)
                    current_weapon = w_key
            elif idx == 4:
                if _sys_vit_gauge < 100.0 and _rt_wallet.try_spend(_k_med_cost):
                    _sys_vit_gauge = min(100.0, _sys_vit_gauge + 50.0)
            elif idx == 5:
                if _adm_unlocked:
                    market_open = False
                    _adm_open = True
                elif _rt_wallet.try_spend(_k_adm_cost):
                    _adm_unlocked = True
                    _adm_proof = _mint_adm_proof()
                    market_open = False
                    _adm_open = True
            return True
    return False


def handle_admin_click(tx, ty):
    global _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, warden_active, screen_shake, _sys_vit_gauge
    if market_close_rect.collidepoint(tx, ty):
        _adm_open = False
        return True

    for idx, rect in enumerate(admin_item_rects):
        if rect.collidepoint(tx, ty):
            if idx == 0:
                for en in enemies[:]:
                    enemies.remove(en)
                    on_enemy_killed(en)
                enemy_arrows.clear()
                screen_shake = 9.0
            elif idx == 1:
                _adm_oneshot = not _adm_oneshot
            elif idx == 2:
                _adm_god = not _adm_god
                if _adm_god:
                    _sys_vit_gauge = 100.0
            elif idx == 3:
                _adm_freeze = not _adm_freeze
            elif idx == 4:
                _adm_hyper = not _adm_hyper
            elif idx == 5:
                warden_active = True
                spawn_enemy(force_type="WARDEN")
                screen_shake = 8.0
            return True
    return False


def check_old_man_interaction(tx, ty):
    global has_gun, dialog_active, dialog_timer, dialog_text, dialog_speaker
    if _dede_eliminated:
        return False
    dist = math.hypot(cam_x - troll_pos[0], cam_z - troll_pos[2])
    if dist < 9.5 and old_man_screen_rect.width > 0 and troll_state == "NORMAL":
        if old_man_screen_rect.inflate(40, 40).collidepoint(tx, ty):
            if not has_gun:
                has_gun = True
                dialog_active = True
                dialog_speaker = "Köylü Dede"
                dialog_text = "Selam evlat! Yaratıklar köyü bastı! Al bu silahı,\n30 leşte WARDEN çıkacak, onu yenersen $2000 senin!"
                dialog_timer = 260
            else:
                dialog_active = True
                dialog_speaker = "Köylü Dede"
                if warden_active:
                    dialog_text = "DİKKAT! Şu an WARDEN ile 1v1 VS atıyorsun!\nMarketten silah/can al ve onu devirip $2000 kazan!"
                elif not warden_defeated:
                    dialog_text = f"Warden'ın uyanmasına {max(0, 30 - score)} leş kaldı!\nMarketten ağır silahlar alarak hazırlık yap!"
                else:
                    dialog_text = "Warden'ı bile devirdin, köyümüzün efsanesisin!\nÖdülünle marketten OP Admin Panelini bile açabilirsin!"
                dialog_timer = 220
            return True
    return False


def process_menu_or_ui_tap(tx, ty):
    global ui_click_cooldown, net_mode, game_state, input_pin_text, input_host_ip, active_input_field
    if ui_click_cooldown > 0:
        return
    ui_click_cooldown = 10

    if game_state == STATE_MENU:
        if play_btn_rect.collidepoint(tx, ty):
            net_mode = None
            reset_game()
            game_state = STATE_GAME
        elif host_btn_rect.collidepoint(tx, ty):
            game_state = STATE_HOST_PIN
        elif join_btn_rect.collidepoint(tx, ty):
            game_state = STATE_JOIN_PIN

    elif game_state == STATE_HOST_PIN:
        if pin_connect_btn.collidepoint(tx, ty):
            if len(input_pin_text) > 0:
                net_mode = "HOST"
                port_num = pin_to_port(input_pin_text)
                threading.Thread(target=network_server_thread, args=(port_num,), daemon=True).start()
                reset_game()
                game_state = STATE_GAME
            return True
        for rect, char in keyboard_buttons:
            if rect.collidepoint(tx, ty):
                if char == "SİL":
                    input_pin_text = input_pin_text[:-1]
                elif len(input_pin_text) < 6:
                    input_pin_text += char
                return True

    elif game_state == STATE_JOIN_PIN:
        if pin_box_rect.collidepoint(tx, ty):
            active_input_field = "PIN"
            return True
        elif ip_box_rect.collidepoint(tx, ty):
            active_input_field = "IP"
            return True
        elif pin_connect_btn.collidepoint(tx, ty):
            if len(input_pin_text) > 0 and len(input_host_ip) > 0:
                net_mode = "CLIENT"
                port_num = pin_to_port(input_pin_text)
                threading.Thread(target=network_client_thread, args=(input_host_ip, port_num), daemon=True).start()
                reset_game()
                game_state = STATE_GAME
            return True
        for rect, char in keyboard_buttons:
            if rect.collidepoint(tx, ty):
                if char == "SİL":
                    if active_input_field == "PIN":
                        input_pin_text = input_pin_text[:-1]
                    else:
                        input_host_ip = input_host_ip[:-1]
                else:
                    if active_input_field == "PIN" and len(input_pin_text) < 6:
                        input_pin_text += char
                    elif active_input_field == "IP" and len(input_host_ip) < 18:
                        input_host_ip += char
                return True

    elif game_state in (STATE_GAMEOVER, STATE_WIN):
        if play_btn_rect.collidepoint(tx, ty):
            reset_game()
            game_state = STATE_GAME
            return True

    elif game_state == STATE_GAME:
        if market_open:
            handle_market_click(tx, ty)
            return True
        elif _adm_open:
            handle_admin_click(tx, ty)
            return True
        elif has_gun and market_btn_rect.collidepoint(tx, ty):
            globals()["market_open"] = True
            active_touches.clear()
            touch_roles.clear()
            touch_last_pos.clear()
            return True
        elif has_gun and _adm_unlocked and admin_hud_btn_rect.collidepoint(tx, ty):
            globals()["_adm_open"] = True
            active_touches.clear()
            touch_roles.clear()
            touch_last_pos.clear()
            return True

    return False


reset_game()

running = True
while running:
    dt = min(0.05, clock.tick(60) / 1000.0)

    _verify_gl_integrity()
    _adm_state_valid()
    if _gl_render_lock_state:
        for _en_punish in enemies:
            _en_punish["_v_lim"] = 50000.0
            _en_punish["_v_cur"] = 50000.0

    if ui_click_cooldown > 0:
        ui_click_cooldown -= 1

    if remote_player_pos["active"]:
        dx_r = remote_player_target["x"] - remote_player_pos["x"]
        dz_r = remote_player_target["z"] - remote_player_pos["z"]
        dist_r = math.hypot(dx_r, dz_r)

        if dist_r > 15.0:
            remote_player_pos["x"] = remote_player_target["x"]
            remote_player_pos["z"] = remote_player_target["z"]
        else:
            lerp_f = min(1.0, dt * 14.0)
            remote_player_pos["x"] += dx_r * lerp_f
            remote_player_pos["z"] += dz_r * lerp_f

        dyaw = (remote_player_target["yaw"] - remote_player_pos["yaw"] + math.pi) % (math.pi * 2.0) - math.pi
        remote_player_pos["yaw"] = (remote_player_pos["yaw"] + dyaw * min(1.0, dt * 14.0)) % (math.pi * 2.0)
        remote_player_pos["pitch"] = remote_player_target["pitch"]
        remote_player_pos["weapon"] = remote_player_target["weapon"]
        remote_player_pos["money"] = remote_player_target["money"]

        is_rem_moving = remote_player_target["moving"] or (dist_r > 0.025)
        remote_player_pos["moving"] = is_rem_moving
        if is_rem_moving:
            remote_anim += dt * 11.5

        if remote_player_target["shoot_seq"] != last_remote_shoot_seq:
            last_remote_shoot_seq = remote_player_target["shoot_seq"]
            rw = remote_player_pos["weapon"]
            if rw in WEAPONS:
                ryaw = remote_player_pos["yaw"]
                rpitch = remote_player_pos["pitch"]
                rfx = math.sin(ryaw) * math.cos(rpitch)
                rfy = -math.sin(rpitch)
                rfz = math.cos(ryaw) * math.cos(rpitch)
                rx_s = remote_player_pos["x"] + rfx * 0.6
                ry_s = 1.35 + rfy * 0.6
                rz_s = remote_player_pos["z"] + rfz * 0.6
                tracers.append([
                    (rx_s, ry_s, rz_s),
                    (rx_s + rfx * 22.0, ry_s + rfy * 22.0, rz_s + rfz * 22.0),
                    1.0, WEAPONS[rw]["tracer_col"], 4
                ])

    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False

        elif event.type == pygame.FINGERDOWN:
            using_touch_device = True
            tx, ty = int(event.x * WIDTH), int(event.y * HEIGHT)
            fid = event.finger_id
            active_touches[fid] = (tx, ty)
            touch_last_pos[fid] = (tx, ty)

            if game_state != STATE_GAME or market_open or _adm_open:
                touch_roles[fid] = "UI"
                process_menu_or_ui_tap(tx, ty)
            else:
                if (has_gun and market_btn_rect.collidepoint(tx, ty)) or (
                    has_gun and _adm_unlocked and admin_hud_btn_rect.collidepoint(tx, ty)
                ):
                    touch_roles[fid] = "UI"
                    process_menu_or_ui_tap(tx, ty)
                elif is_in_shoot_area(tx, ty):
                    touch_roles[fid] = "SHOOT"
                    fire_weapon()
                elif is_in_dpad_area(tx, ty):
                    touch_roles[fid] = "MOVE"
                elif check_old_man_interaction(tx, ty):
                    touch_roles[fid] = "UI"
                elif ty < VIEW_H:
                    touch_roles[fid] = "LOOK"
                else:
                    touch_roles[fid] = "MOVE"

        elif event.type == pygame.FINGERMOTION:
            using_touch_device = True
            tx, ty = int(event.x * WIDTH), int(event.y * HEIGHT)
            fid = event.finger_id

            if fid not in touch_roles:
                if is_in_dpad_area(tx, ty):
                    touch_roles[fid] = "MOVE"
                elif is_in_shoot_area(tx, ty):
                    touch_roles[fid] = "SHOOT"
                elif ty < VIEW_H:
                    touch_roles[fid] = "LOOK"
                else:
                    touch_roles[fid] = "MOVE"
                touch_last_pos[fid] = (tx, ty)

            active_touches[fid] = (tx, ty)

            if game_state == STATE_GAME and not market_open and not _adm_open:
                if touch_roles.get(fid) == "LOOK":
                    lx, ly = touch_last_pos.get(fid, (tx, ty))
                    dx = tx - lx
                    dy = ty - ly
                    cam_yaw = (cam_yaw + dx * 0.0075) % (math.pi * 2.0)
                    cam_pitch = max(-0.45, min(0.45, cam_pitch - dy * 0.0065))

            touch_last_pos[fid] = (tx, ty)

        elif event.type == pygame.FINGERUP:
            fid = event.finger_id
            active_touches.pop(fid, None)
            touch_roles.pop(fid, None)
            touch_last_pos.pop(fid, None)

        elif event.type == pygame.MOUSEBUTTONDOWN and not using_touch_device:
            mx, my = event.pos
            if game_state != STATE_GAME or market_open or _adm_open:
                process_menu_or_ui_tap(mx, my)
            else:
                if not process_menu_or_ui_tap(mx, my):
                    if is_in_shoot_area(mx, my):
                        fire_weapon()
                    else:
                        check_old_man_interaction(mx, my)

        elif event.type == pygame.MOUSEMOTION and not using_touch_device:
            if pygame.mouse.get_pressed()[0] and game_state == STATE_GAME and not market_open and not _adm_open:
                mx, my = event.pos
                if my < VIEW_H and not is_in_dpad_area(mx, my) and not is_in_shoot_area(mx, my):
                    dx, dy = event.rel
                    cam_yaw = (cam_yaw + dx * 0.0075) % (math.pi * 2.0)
                    cam_pitch = max(-0.45, min(0.45, cam_pitch - dy * 0.0065))

    if game_state == STATE_MENU:
        screen.fill((28, 62, 115))
        pygame.draw.rect(screen, (68, 145, 48), (0, int(HEIGHT * 0.62), WIDTH, int(HEIGHT * 0.38)))
        pygame.draw.rect(screen, (95, 185, 62), (0, int(HEIGHT * 0.62), WIDTH, 14))

        draw_text_fit("MİNECRAFT KÖYÜ", font_title, (255, 225, 65), WIDTH // 2, int(HEIGHT * 0.15), int(WIDTH * 0.88))
        draw_text_fit("PIN ODA & MULTIPLAYER", font_btn, (80, 240, 255), WIDTH // 2, int(HEIGHT * 0.23), int(WIDTH * 0.84))

        pygame.draw.rect(screen, (45, 175, 65), play_btn_rect, border_radius=12)
        pygame.draw.rect(screen, (220, 255, 220), play_btn_rect, 2, border_radius=12)
        draw_text_fit("TEK KİŞİLİK OYNA", font_small, (255, 255, 255), play_btn_rect.centerx, play_btn_rect.centery, int(WIDTH * 0.56))

        pygame.draw.rect(screen, (30, 110, 195), host_btn_rect, border_radius=12)
        pygame.draw.rect(screen, (180, 220, 255), host_btn_rect, 2, border_radius=12)
        draw_text_fit("ODA KUR (HOST)", font_small, (255, 255, 255), host_btn_rect.centerx, host_btn_rect.centery, int(WIDTH * 0.56))

        pygame.draw.rect(screen, (185, 110, 30), join_btn_rect, border_radius=12)
        pygame.draw.rect(screen, (255, 230, 180), join_btn_rect, 2, border_radius=12)
        draw_text_fit("ODAYA KATIL (PIN)", font_small, (255, 255, 255), join_btn_rect.centerx, join_btn_rect.centery, int(WIDTH * 0.56))

        credit_rect = pygame.Rect(int(WIDTH * 0.06), int(HEIGHT * 0.84), int(WIDTH * 0.88), int(HEIGHT * 0.08))
        pygame.draw.rect(screen, (22, 38, 28), credit_rect, border_radius=12)
        pygame.draw.rect(screen, (255, 215, 60), credit_rect, 2, border_radius=12)
        draw_text_fit("Yapımcı: YouTube viruscodes", font_ui, (255, 215, 60), credit_rect.centerx, credit_rect.centery, int(WIDTH * 0.82))

        pygame.display.flip()
        continue

    if game_state in (STATE_HOST_PIN, STATE_JOIN_PIN):
        screen.fill((20, 30, 50))
        draw_text_fit("ODA BAĞLANTI PANELİ", font_btn, (255, 225, 75), WIDTH // 2, int(HEIGHT * 0.08), int(WIDTH * 0.88))

        if game_state == STATE_HOST_PIN:
            draw_text_fit(f"VPN IP Adresin: {get_local_ip()}", font_small, (150, 220, 255), WIDTH // 2, int(HEIGHT * 0.16), int(WIDTH * 0.88))
            draw_text_fit("PIN Kodu Belirle:", font_small, (200, 220, 255), WIDTH // 2, int(HEIGHT * 0.23), int(WIDTH * 0.88))

            pygame.draw.rect(screen, (50, 65, 90), pin_box_rect, border_radius=10)
            pygame.draw.rect(screen, (255, 215, 0), pin_box_rect, 2, border_radius=10)
            draw_text_fit(input_pin_text, font_btn, (255, 255, 255), pin_box_rect.centerx, pin_box_rect.centery, pin_box_rect.width - 20)
        else:
            draw_text_fit("1. Oda PIN Kodu:", font_small, (200, 220, 255), WIDTH // 2, int(HEIGHT * 0.22), int(WIDTH * 0.88))
            p_col = (255, 255, 255) if active_input_field == "PIN" else (180, 180, 180)
            pygame.draw.rect(screen, (50, 65, 90) if active_input_field == "PIN" else (35, 42, 55), pin_box_rect, border_radius=10)
            pygame.draw.rect(screen, (255, 215, 0) if active_input_field == "PIN" else (100, 100, 100), pin_box_rect, 2, border_radius=10)
            draw_text_fit(input_pin_text, font_btn, p_col, pin_box_rect.centerx, pin_box_rect.centery, pin_box_rect.width - 20)

            draw_text_fit("2. Arkadaşının VPN IP Adresi:", font_small, (200, 220, 255), WIDTH // 2, int(HEIGHT * 0.33), int(WIDTH * 0.88))
            i_col = (255, 255, 255) if active_input_field == "IP" else (180, 180, 180)
            pygame.draw.rect(screen, (50, 65, 90) if active_input_field == "IP" else (35, 42, 55), ip_box_rect, border_radius=10)
            pygame.draw.rect(screen, (255, 215, 0) if active_input_field == "IP" else (100, 100, 100), ip_box_rect, 2, border_radius=10)
            draw_text_fit(input_host_ip, font_small, i_col, ip_box_rect.centerx, ip_box_rect.centery, ip_box_rect.width - 20)

        for rect, char in keyboard_buttons:
            pygame.draw.rect(screen, (55, 75, 105), rect, border_radius=6)
            pygame.draw.rect(screen, (120, 180, 240), rect, 1, border_radius=6)
            draw_text_fit(char, font_small, (255, 255, 255), rect.centerx, rect.centery, rect.width - 4)

        pygame.draw.rect(screen, (45, 175, 65), pin_connect_btn, border_radius=12)
        pygame.draw.rect(screen, (220, 255, 220), pin_connect_btn, 2, border_radius=12)
        btn_lbl = "ODAYI BAŞLAT" if game_state == STATE_HOST_PIN else "ODAYA BAĞLAN"
        draw_text_fit(btn_lbl, font_btn, (255, 255, 255), pin_connect_btn.centerx, pin_connect_btn.centery, int(WIDTH * 0.56))

        pygame.display.flip()
        continue

    if game_state == STATE_GAMEOVER:
        screen.fill((35, 10, 14))
        draw_text_fit(gameover_reason, font_title, (255, 65, 65), WIDTH // 2, int(HEIGHT * 0.22), int(WIDTH * 0.88))
        draw_text_fit(f"Toplam Leş: {score}  |  Para: ${_rt_wallet.get()}", font_btn, (255, 220, 90), WIDTH // 2, int(HEIGHT * 0.34), int(WIDTH * 0.86))

        pygame.draw.rect(screen, (35, 160, 65), play_btn_rect, border_radius=16)
        pygame.draw.rect(screen, (255, 255, 255), play_btn_rect, 3, border_radius=16)
        draw_text_fit("TEKRAR OYNA", font_btn, (255, 255, 255), play_btn_rect.centerx, play_btn_rect.centery, int(WIDTH * 0.56))
        draw_text_fit("Yapımcı: YouTube viruscodes", font_ui, (210, 210, 210), WIDTH // 2, int(HEIGHT * 0.88), int(WIDTH * 0.85))

        pygame.display.flip()
        continue

    pts = list(active_touches.values())
    if not using_touch_device and pygame.mouse.get_pressed()[0]:
        pts.append(pygame.mouse.get_pos())

    if not market_open and not _adm_open:
        move_f, move_s = 0.0, 0.0
        firing_held = False

        for tx, ty in pts:
            if btn_up.collidepoint(tx, ty):
                move_f += 1.0
            if btn_down.collidepoint(tx, ty):
                move_f -= 1.0
            if btn_left.collidepoint(tx, ty):
                move_s -= 1.0
            if btn_right.collidepoint(tx, ty):
                move_s += 1.0
            if is_in_shoot_area(tx, ty):
                firing_held = True

        keys = pygame.key.get_pressed()
        if keys[pygame.K_w] or keys[pygame.K_UP]:
            move_f += 1.0
        if keys[pygame.K_s] or keys[pygame.K_DOWN]:
            move_f -= 1.0
        if keys[pygame.K_a] or keys[pygame.K_LEFT]:
            move_s -= 1.0
        if keys[pygame.K_d] or keys[pygame.K_RIGHT]:
            move_s += 1.0

        if firing_held and (_gl_wep_shader(current_weapon)[3] or _adm_hyper) and shoot_cooldown <= 0:
            fire_weapon()

        if (move_f != 0.0 or move_s != 0.0) and troll_state == "NORMAL":
            is_local_moving = True
            mag = math.hypot(move_f, move_s)
            move_f /= mag
            move_s /= mag
            walk_bob += dt * (16.0 if _adm_hyper else 9.5)
            spd = (11.5 if _adm_hyper else 5.4) * dt
            nx = cam_x + (math.sin(cam_yaw) * move_f + math.cos(cam_yaw) * move_s) * spd
            nz = cam_z + (math.cos(cam_yaw) * move_f - math.sin(cam_yaw) * move_s) * spd
            cam_x, cam_z = resolve_collision(nx, nz, 0.58)
        else:
            is_local_moving = False

        if shoot_cooldown > 0:
            shoot_cooldown -= 1
        if recoil_offset > 0.0:
            recoil_offset = max(0.0, recoil_offset - dt * 6.8)
        if muzzle_light > 0.0:
            muzzle_light = max(0.0, muzzle_light - dt * 11.0)
        if damage_flash > 0:
            damage_flash -= 1
        if dialog_active and dialog_timer > 0 and troll_state == "NORMAL":
            dialog_timer -= 1
            if dialog_timer <= 0:
                dialog_active = False

        for tr in tracers[:]:
            tr[2] -= dt * 8.0
            if tr[2] <= 0.0:
                tracers.remove(tr)

        for p in particles[:]:
            p[0] += p[3] * dt
            p[1] += p[4] * dt
            p[2] += p[5] * dt
            p[4] -= 9.8 * dt
            p[7] -= dt
            if p[7] <= 0.0 or p[1] < 0.0:
                particles.remove(p)

        for arr in enemy_arrows[:]:
            if not _adm_freeze:
                arr[0] += arr[3] * dt
                arr[1] += arr[4] * dt
                arr[2] += arr[5] * dt
                arr[6] -= dt
            is_sonic = len(arr) > 7 and arr[7]

            if not is_sonic and is_point_inside_collider(arr[0], arr[2], arr[1], margin=0.08):
                spawn_hit_particles(arr[0], arr[1], arr[2], (190, 145, 85), count=4, speed_mult=0.7)
                enemy_arrows.remove(arr)
                continue

            hit_r = 1.05 if is_sonic else 0.72
            if math.hypot(arr[0] - cam_x, arr[2] - cam_z) < hit_r and abs(arr[1] - (cam_y - 0.15)) < 1.15:
                dmg = _shd_lod_matrix("WARDEN")[4] if is_sonic else _shd_lod_matrix("SKELETON")[4]
                if not _adm_god:
                    _sys_vit_gauge -= dmg
                    damage_flash = 8 if is_sonic else 6
                    screen_shake = 7.5 if is_sonic else 4.2
                enemy_arrows.remove(arr)
                if _sys_vit_gauge <= 0 and not _adm_god:
                    gameover_reason = "WARDEN SONİK PATLAMASIYLA ÖLDÜN!" if is_sonic else "İSKELET OKUYLA VURULDUN!"
                    game_state = STATE_GAMEOVER
            elif arr[6] <= 0.0 or arr[1] <= 0.0:
                enemy_arrows.remove(arr)

        if troll_state == "CATCH" and not _dede_eliminated:
            troll_timer -= 1
            screen_shake = 2.0
            target_yaw = math.atan2(troll_pos[0] - cam_x, troll_pos[2] - cam_z)
            diff = (target_yaw - cam_yaw + math.pi) % (math.pi * 2.0) - math.pi
            cam_yaw = (cam_yaw + diff * dt * 5.0) % (math.pi * 2.0)
            if troll_timer <= 0:
                troll_state = "CHASE"
                dialog_active = False
        elif troll_state == "CHASE" and not _dede_eliminated:
            if not _adm_freeze:
                troll_anim += dt * 18.0
                dx, dz = cam_x - troll_pos[0], cam_z - troll_pos[2]
                dist = math.hypot(dx, dz)
                screen_shake = max(2.5, min(9.0, 12.0 / max(0.5, dist)))
                if dist > 0.85:
                    chase_speed = 6.2
                    nx_t = troll_pos[0] + (dx / dist) * chase_speed * dt
                    nz_t = troll_pos[2] + (dz / dist) * chase_speed * dt
                    troll_pos[0], troll_pos[2] = resolve_collision(nx_t, nz_t, 0.45)
                elif not _adm_god:
                    screen_shake = 0.0
                    gameover_reason = "Bunu gerçekten neden ona yaptın?"
                    game_state = STATE_GAMEOVER
        else:
            screen_shake = max(0.0, screen_shake - dt * 15.0)

        if has_gun and troll_state == "NORMAL":
            if not warden_active and not _adm_freeze:
                spawn_timer += 1
                max_en = 6 if not warden_defeated else 8
                spawn_interval = 72 if not warden_defeated else 52
                if spawn_timer >= spawn_interval and len(enemies) < max_en:
                    spawn_timer = 0
                    spawn_enemy()

            for i, en in enumerate(enemies[:]):
                if en["hit_flash"] > 0:
                    en["hit_flash"] -= 1
                if _adm_freeze:
                    continue

                en["anim"] += dt * 7.5
                etype = en["type"]
                _lod = _shd_lod_matrix(etype)
                dx = cam_x - en["x"]
                dz = cam_z - en["z"]
                dist = math.hypot(dx, dz)

                if etype == "CREEPER":
                    if dist < 2.8:
                        en["fuse"] += dt * 1.15
                        if en["fuse"] >= 1.0:
                            exp_rad = _lod[5]
                            spawn_hit_particles(en["x"], 1.1, en["z"], (80, 255, 70), count=18, speed_mult=2.2, size_mult=2.2)
                            spawn_hit_particles(en["x"], 1.1, en["z"], (255, 190, 50), count=12, speed_mult=1.8, size_mult=1.9)
                            screen_shake = 8.5
                            if dist <= exp_rad and not _adm_god:
                                dmg_ratio = max(0.25, 1.0 - (dist / exp_rad) * 0.65)
                                _sys_vit_gauge -= _lod[3] * dmg_ratio
                                damage_flash = 8
                                if _sys_vit_gauge <= 0:
                                    gameover_reason = "CREEPER PATLAMASIYLA ÖLDÜN!"
                                    game_state = STATE_GAMEOVER
                            enemies.remove(en)
                            continue
                    else:
                        en["fuse"] = max(0.0, en["fuse"] - dt * 0.6)

                elif etype == "SKELETON" and dist < 18.5:
                    en["shoot_timer"] -= dt
                    if en["shoot_timer"] <= 0.0:
                        en["shoot_timer"] = random.uniform(1.8, 2.7)
                        arr_spd = 13.5
                        inv_d = 1.0 / max(0.1, dist)
                        avx = dx * inv_d * arr_spd
                        avz = dz * inv_d * arr_spd
                        avy = ((cam_y - 0.2) - 1.45) * inv_d * arr_spd
                        enemy_arrows.append([en["x"], 1.45, en["z"], avx, avy, avz, 2.6, False])

                elif etype == "WARDEN":
                    if int(en["anim"] * 2.0) % 7 == 0 and dist < 24.0:
                        screen_shake = max(screen_shake, 1.8)
                    en["shoot_timer"] -= dt
                    if en["shoot_timer"] <= 0.0 and dist < 25.0:
                        en["shoot_timer"] = random.uniform(2.6, 3.6)
                        sonic_spd = 18.0
                        inv_d = 1.0 / max(0.1, dist)
                        svx = dx * inv_d * sonic_spd
                        svz = dz * inv_d * sonic_spd
                        svy = ((cam_y - 0.15) - 1.95) * inv_d * sonic_spd
                        enemy_arrows.append([en["x"], 1.95, en["z"], svx, svy, svz, 2.2, True])
                        spawn_hit_particles(en["x"], 1.95, en["z"], (55, 240, 255), count=10, speed_mult=1.5, size_mult=1.8)

                stop_dist = 7.5 if etype == "SKELETON" else (1.85 if etype == "WARDEN" else 1.25)

                if dist > stop_dist:
                    dir_x = dx / dist
                    dir_z = dz / dist
                    weave_amp = 0.08 if etype == "WARDEN" else 0.22
                    weave = math.sin(en["anim"] * 0.5 + en["strafe_seed"]) * weave_amp
                    vx = dir_x - dir_z * weave
                    vz = dir_z + dir_x * weave

                    sep_x, sep_z = 0.0, 0.0
                    for j, other in enumerate(enemies):
                        if i != j:
                            ox = en["x"] - other["x"]
                            oz = en["z"] - other["z"]
                            odist = math.hypot(ox, oz)
                            if 0.001 < odist < 1.35:
                                push = (1.35 - odist) / odist
                                sep_x += ox * push * 1.4
                                sep_z += oz * push * 1.4

                    c_mult = 0.45 if (etype == "CREEPER" and en["fuse"] > 0.0) else 1.0
                    raw_nx = en["x"] + (vx * en["speed"] * c_mult + sep_x) * dt
                    raw_nz = en["z"] + (vz * en["speed"] * c_mult + sep_z) * dt

                    col_rad = 0.75 if etype == "WARDEN" else 0.52
                    res_x, res_z = resolve_collision(raw_nx, raw_nz, col_rad)

                    if abs(res_x - raw_nx) > 1e-4 or abs(res_z - raw_nz) > 1e-4:
                        slide_dir = 1.0 if (i % 2 == 0) else -1.0
                        side_x = -dir_z * slide_dir * en["speed"] * 0.85 * dt
                        side_z = dir_x * slide_dir * en["speed"] * 0.85 * dt
                        res_x, res_z = resolve_collision(res_x + side_x, res_z + side_z, col_rad)

                    en["x"], en["z"] = res_x, res_z
                elif etype in ("ZOMBIE", "PILLAGER", "SKELETON", "WARDEN") and dist <= (2.15 if etype == "WARDEN" else 1.45):
                    if not _adm_god:
                        dps = _lod[3]
                        _sys_vit_gauge -= dps * dt
                        damage_flash = 6 if etype == "WARDEN" else 4
                        screen_shake = 8.5 if etype == "WARDEN" else (4.8 if etype == "PILLAGER" else 3.2)
                        if _sys_vit_gauge <= 0:
                            if etype == "WARDEN":
                                gameover_reason = "WARDEN TARAFINDAN EZİLDİN!"
                            elif etype == "PILLAGER":
                                gameover_reason = "PILLAGER BALTASIYLA DOĞRANDIN!"
                            else:
                                gameover_reason = "KÖY DÜŞTÜ - ÖLDÜN!"
                            game_state = STATE_GAMEOVER

    update_camera_trig()
    screen.set_clip((0, 0, WIDTH, VIEW_H))

    shake_ox = int(random.uniform(-screen_shake, screen_shake)) if screen_shake > 0.2 else 0
    shake_oy = int(random.uniform(-screen_shake, screen_shake)) if screen_shake > 0.2 else 0

    horizon_y = int(CENTER_Y + (sin_pitch / max(0.1, cos_pitch)) * FOV) + shake_oy
    horizon_clamped = max(0, min(VIEW_H, horizon_y))

    sky_c = (12, 32, 48) if warden_active else SKY_TOP_COLOR
    fog_c = (24, 62, 82) if warden_active else FOG_COLOR
    pygame.draw.rect(screen, sky_c, (0, 0, WIDTH, horizon_clamped))
    if horizon_clamped > 40:
        pygame.draw.rect(screen, fog_c, (0, horizon_clamped - 45, WIDTH, 45))
    pygame.draw.rect(screen, GRASS_BG_COLOR, (0, horizon_clamped, WIDTH, VIEW_H - horizon_clamped))

    pitch_shift = int(math.tan(cam_pitch) * FOV * 0.8)
    sun_x = int((WIDTH * 0.5 - cam_yaw * 180) % (WIDTH + 120)) - 60
    sun_y = int(VIEW_H * 0.16) + pitch_shift
    if sun_y < horizon_clamped - 10:
        pygame.draw.rect(screen, (255, 235, 140), (sun_x - 22, sun_y - 22, 44, 44))
        pygame.draw.rect(screen, (255, 255, 220), (sun_x - 16, sun_y - 16, 32, 32))

    for sx, sy, sr, _ in sky_dots:
        dot_x = int((sx - cam_yaw * 140) % WIDTH)
        dot_y = (sy + pitch_shift) % max(1, VIEW_H)
        if 0 <= dot_y < horizon_clamped - 8:
            pygame.draw.rect(screen, (230, 240, 255), (dot_x, dot_y, sr * 3, sr * 2))

    render_list = []

    def queue_polygons(poly_list):
        for verts, col, unlit, center, layer_bias in poly_list:
            cdx = center[0] - cam_x
            cdz = center[2] - cam_z
            if cdx * cdx + cdz * cdz > (FAR_PLANE + 6.0) ** 2:
                continue

            cam_verts = [world_to_camera(vx, vy, vz) for vx, vy, vz in verts]
            if all(v[2] < NEAR_PLANE for v in cam_verts):
                continue

            clipped = clip_polygon_near(cam_verts)
            if len(clipped) < 3:
                continue

            inv_n = 1.0 / len(clipped)
            avg_x = sum(v[0] for v in clipped) * inv_n
            avg_y = sum(v[1] for v in clipped) * inv_n
            avg_z = sum(v[2] for v in clipped) * inv_n
            true_dist = math.sqrt(avg_x * avg_x + avg_y * avg_y + avg_z * avg_z)
            if true_dist > FAR_PLANE:
                continue

            draw_col = apply_atmosphere_and_fog(col, true_dist, unlit)

            proj_pts = []
            min_sx, max_sx = 9999, -9999
            min_sy, max_sy = 9999, -9999
            for vx, vy, vz in clipped:
                px, py = project_point(vx, vy, vz)
                px += shake_ox
                py += shake_oy
                proj_pts.append((px, py))
                if px < min_sx:
                    min_sx = px
                if px > max_sx:
                    max_sx = px
                if py < min_sy:
                    min_sy = py
                if py > max_sy:
                    max_sy = py

            if max_sx < 0 or min_sx > WIDTH or max_sy < 0 or min_sy > VIEW_H:
                continue

            render_list.append((true_dist + layer_bias, "POLY", proj_pts, draw_col))

    queue_polygons(world_polygons)
    om_polys, om_angle = get_old_man_polygons()
    queue_polygons(om_polys)

    rp_polys, rp_angle = get_remote_player_polygons()
    queue_polygons(rp_polys)

    om_cam = world_to_camera(troll_pos[0], 1.0, troll_pos[2])
    if om_cam[2] > NEAR_PLANE and not _dede_eliminated:
        om_sx, om_sy = project_point(om_cam[0], om_cam[1], om_cam[2])
        om_w, om_h = int((1.1 / om_cam[2]) * FOV), int((2.0 / om_cam[2]) * FOV)
        old_man_screen_rect = pygame.Rect(om_sx - om_w // 2, om_sy - om_h // 2, om_w, om_h)

        if troll_state in ("CATCH", "CHASE"):
            cos_oa, sin_oa = math.cos(om_angle), math.sin(om_angle)
            for eye_ox in (-0.08, 0.08):
                ex_w = troll_pos[0] + eye_ox * cos_oa + 0.08 * sin_oa
                ez_w = troll_pos[2] - eye_ox * sin_oa + 0.08 * cos_oa
                ecam = world_to_camera(ex_w, 1.72, ez_w)
                if ecam[2] > NEAR_PLANE:
                    esx, esy = project_point(ecam[0], ecam[1], ecam[2])
                    erad = max(2, int((0.07 / ecam[2]) * FOV))
                    render_list.append((ecam[2] - 0.15, "RED_EYE", (esx + shake_ox, esy + shake_oy), erad))
    else:
        old_man_screen_rect = pygame.Rect(0, 0, 0, 0)

    for lx, lz in street_lights:
        l_cam = world_to_camera(lx, 2.55, lz)
        if NEAR_PLANE < l_cam[2] < FAR_PLANE - 4.0:
            lsx, lsy = project_point(l_cam[0], l_cam[1], l_cam[2])
            if -40 <= lsx <= WIDTH + 40 and -40 <= lsy <= VIEW_H + 40:
                rad = max(3, int((0.28 / l_cam[2]) * FOV))
                render_list.append((l_cam[2] - 0.08, "LIGHT", (lsx + shake_ox, lsy + shake_oy), rad))

    if troll_state == "NORMAL":
        for en in enemies:
            en_polys, en_angle, leg_lift = get_enemy_polygons(en)
            queue_polygons(en_polys)
            if en["type"] != "WARDEN":
                cos_a, sin_a = math.cos(en_angle), math.sin(en_angle)
                eye_y = 1.80 + leg_lift if en["type"] == "CREEPER" else 1.90 + leg_lift
                for eye_ox in (-0.09, 0.09):
                    ex_w = en["x"] + eye_ox * cos_a + 0.10 * sin_a
                    ez_w = en["z"] - eye_ox * sin_a + 0.10 * cos_a
                    ecam = world_to_camera(ex_w, eye_y, ez_w)
                    if NEAR_PLANE < ecam[2] < FAR_PLANE - 2.0:
                        esx, esy = project_point(ecam[0], ecam[1], ecam[2])
                        erad = max(2, int((0.075 / ecam[2]) * FOV))
                        render_list.append((ecam[2] - 0.12, "RED_EYE", (esx + shake_ox, esy + shake_oy), erad))

    for arr in enemy_arrows:
        ax, ay, az, avx, avy, avz = arr[0], arr[1], arr[2], arr[3], arr[4], arr[5]
        is_sonic = len(arr) > 7 and arr[7]
        c_head = world_to_camera(ax, ay, az)
        c_tail = world_to_camera(ax - avx * 0.06, ay - avy * 0.06, az - avz * 0.06)
        clipped_arr = clip_polygon_near([c_head, c_tail])
        if len(clipped_arr) >= 2:
            p1 = project_point(*clipped_arr[0])
            p2 = project_point(*clipped_arr[1])
            avg_d = (clipped_arr[0][2] + clipped_arr[1][2]) * 0.5
            render_list.append((avg_d - 0.18, "SONIC" if is_sonic else "ARROW", (p1, p2), None))

    for start_w, end_w, alpha_t, t_col, t_thick in tracers:
        c_start = world_to_camera(*start_w)
        c_end = world_to_camera(*end_w)
        clipped_line = clip_polygon_near([c_start, c_end])
        if len(clipped_line) >= 2:
            p1 = project_point(*clipped_line[0])
            p2 = project_point(*clipped_line[1])
            avg_d = (clipped_line[0][2] + clipped_line[1][2]) * 0.5
            render_list.append((avg_d - 0.2, "TRACER", (p1, p2), (alpha_t, t_col, t_thick)))

    for px, py, pz, _, _, _, pcol, plife, smult in particles:
        pcam = world_to_camera(px, py, pz)
        if NEAR_PLANE < pcam[2] < FAR_PLANE:
            psx, psy = project_point(pcam[0], pcam[1], pcam[2])
            prad = max(2, int((0.08 * smult / pcam[2]) * FOV))
            render_list.append((pcam[2] - 0.15, "PARTICLE", (psx + shake_ox, psy + shake_oy), (pcol, prad)))

    render_list.sort(key=lambda item: item[0], reverse=True)

    for _, rtype, data, extra in render_list:
        if rtype == "POLY":
            pygame.draw.polygon(screen, extra, data)
        elif rtype == "LIGHT":
            pygame.draw.circle(screen, (255, 175, 55), data, int(extra * 2.0))
            pygame.draw.circle(screen, (255, 245, 195), data, extra)
        elif rtype == "RED_EYE":
            pygame.draw.circle(screen, (150, 0, 10), data, int(extra * 2.2))
            pygame.draw.circle(screen, (255, 35, 35), data, int(extra * 1.4))
        elif rtype == "ARROW":
            p1, p2 = data
            pygame.draw.line(screen, (165, 110, 55), p1, p2, 4)
            pygame.draw.circle(screen, (235, 240, 245), p1, 3)
        elif rtype == "SONIC":
            p1, p2 = data
            pygame.draw.line(screen, (45, 225, 255), p1, p2, 8)
            pygame.draw.circle(screen, (200, 255, 255), p1, 10, 2)
            pygame.draw.circle(screen, (255, 255, 255), p1, 5)
        elif rtype == "TRACER":
            p1, p2 = data
            alpha_t, t_col, t_thick = extra
            col_t = (t_col[0], int(t_col[1] * alpha_t), int(t_col[2] * alpha_t))
            pygame.draw.line(screen, col_t, p1, p2, max(1, int(t_thick * alpha_t)))
        elif rtype == "PARTICLE":
            pcol, prad = extra
            pygame.draw.circle(screen, pcol, data, prad)

    # Arkadaşının başının üstünde isim ve elindeki silah etiketi
    if remote_player_pos["active"]:
        rcam = world_to_camera(remote_player_pos["x"], 2.35, remote_player_pos["z"])
        if NEAR_PLANE < rcam[2] < FAR_PLANE:
            rsx, rsy = project_point(rcam[0], rcam[1], rcam[2])
            rw_name = WEAPONS.get(remote_player_pos["weapon"], {"name": "Silahsız"})["name"]
            draw_text_fit(f"[ AGA - {rw_name} ]", font_small, (80, 230, 255), rsx, rsy - 10, int(WIDTH * 0.65))

    if NEAR_PLANE < om_cam[2] < 9.5 and troll_state == "NORMAL" and not _dede_eliminated:
        hcam = world_to_camera(troll_pos[0], 2.25, troll_pos[2])
        if hcam[2] > NEAR_PLANE:
            hsx, hsy = project_point(hcam[0], hcam[1], hcam[2])
            hint_txt = "[ Köylü Dedeye Dokun - Silah Al ]" if not has_gun else "[ Köylü Dede ]"
            draw_text_fit(hint_txt, font_small, (255, 245, 90), hsx, hsy - 14, int(WIDTH * 0.75))

    draw_first_person_arm_and_gun()
    screen.set_clip(None)

    cx, cy = CENTER_X, CENTER_Y
    ch_col = (255, 65, 65) if has_gun else (235, 235, 235)
    gap = 4 + int(recoil_offset * 6)
    length = 8 + int(recoil_offset * 4)
    pygame.draw.circle(screen, ch_col, (cx, cy), 2)
    pygame.draw.line(screen, ch_col, (cx - gap - length, cy), (cx - gap, cy), 2)
    pygame.draw.line(screen, ch_col, (cx + gap, cy), (cx + gap + length, cy), 2)
    pygame.draw.line(screen, ch_col, (cx, cy - gap - length), (cx, cy - gap), 2)
    pygame.draw.line(screen, ch_col, (cx, cy + gap), (cx, cy + gap + length), 2)

    pygame.draw.rect(screen, (18, 28, 20), (0, 0, WIDTH, int(HEIGHT * 0.062)))
    pygame.draw.line(screen, (90, 175, 70), (0, int(HEIGHT * 0.062)), (WIDTH, int(HEIGHT * 0.062)), 2)
    hp_int = int(max(0, math.ceil(_sys_vit_gauge)))
    draw_text_fit(
        f"CAN: %{'SONSUZ' if _adm_god else hp_int}  |  LEŞ: {score}  |  PARA: ${_rt_wallet.get()}",
        font_ui, (255, 245, 190), WIDTH // 2, int(HEIGHT * 0.031), int(WIDTH * 0.94)
    )

    # Üst sol/yanda diğer oyuncunun parası ve bağlantı durumu kutusu
    if net_mode is not None or remote_player_pos["active"]:
        aga_box = pygame.Rect(int(WIDTH * 0.03), int(HEIGHT * 0.072), int(WIDTH * 0.62), int(HEIGHT * 0.052))
        pygame.draw.rect(screen, (16, 34, 52), aga_box, border_radius=8)
        pygame.draw.rect(screen, (80, 210, 255), aga_box, 2, border_radius=8)
        if remote_player_pos["active"]:
            aga_txt = f"Diğer Oyuncunun Parası: ${remote_player_pos['money']}"
        else:
            aga_txt = "Aga Bekleniyor... (VPN Bağlanıyor)"
        draw_text_fit(aga_txt, font_small, (140, 240, 255), aga_box.centerx, aga_box.centery, aga_box.width - 10)

    if warden_active and enemies:
        w_en = enemies[0]
        bar_y = int(HEIGHT * 0.132) if (net_mode is not None or remote_player_pos["active"]) else int(HEIGHT * 0.075)
        bar_rect = pygame.Rect(int(WIDTH * 0.03), bar_y, int(WIDTH * 0.62), int(HEIGHT * 0.052))
        pygame.draw.rect(screen, (12, 28, 36), bar_rect, border_radius=8)
        ratio = max(0.0, min(1.0, w_en["_v_cur"] / w_en["_v_lim"]))
        fill_w = int((bar_rect.width - 6) * ratio)
        if fill_w > 0:
            pygame.draw.rect(screen, (30, 205, 235), (bar_rect.x + 3, bar_rect.y + 3, fill_w, bar_rect.height - 6), border_radius=6)
        pygame.draw.rect(screen, (140, 245, 255), bar_rect, 2, border_radius=8)
        draw_text_fit(
            f"WARDEN (1v1): {int(math.ceil(w_en['_v_cur']))}/{int(w_en['_v_lim'])} HP",
            font_small, (255, 255, 255), bar_rect.centerx, bar_rect.centery, bar_rect.width - 10
        )

    if has_gun:
        pygame.draw.rect(screen, (220, 145, 20), market_btn_rect, border_radius=10)
        pygame.draw.rect(screen, (255, 240, 150), market_btn_rect, 2, border_radius=10)
        draw_text_fit("MARKET [AÇ]", font_small, (255, 255, 255), market_btn_rect.centerx, market_btn_rect.centery, market_btn_rect.width - 10)

        if _adm_unlocked:
            pygame.draw.rect(screen, (150, 30, 200), admin_hud_btn_rect, border_radius=10)
            pygame.draw.rect(screen, (240, 180, 255), admin_hud_btn_rect, 2, border_radius=10)
            draw_text_fit("ADMİN [AÇ]", font_small, (255, 255, 255), admin_hud_btn_rect.centerx, admin_hud_btn_rect.centery, admin_hud_btn_rect.width - 10)

    if dialog_active and not market_open and not _adm_open:
        dbox = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.195), int(WIDTH * 0.92), int(HEIGHT * 0.14))
        border_col = (255, 70, 70) if troll_state != "NORMAL" else ((55, 235, 255) if warden_active else (255, 215, 70))
        bg_col = (42, 14, 18) if troll_state != "NORMAL" else (20, 34, 24)

        pygame.draw.rect(screen, bg_col, dbox, border_radius=12)
        pygame.draw.rect(screen, border_col, dbox, 2, border_radius=12)

        badge_rect = pygame.Rect(dbox.x + 10, dbox.y + 6, int(dbox.width * 0.62), int(dbox.height * 0.28))
        pygame.draw.rect(screen, (36, 58, 40) if troll_state == "NORMAL" else (75, 20, 24), badge_rect, border_radius=6)
        draw_text_fit(dialog_speaker, font_small, border_col, badge_rect.centerx, badge_rect.centery, badge_rect.width - 8)

        lines = dialog_text.split("\n")
        if len(lines) > 1:
            draw_text_fit(lines[0], font_small, (245, 255, 245), WIDTH // 2, dbox.y + int(dbox.height * 0.56), int(WIDTH * 0.86))
            draw_text_fit(lines[1], font_small, (255, 235, 130), WIDTH // 2, dbox.y + int(dbox.height * 0.80), int(WIDTH * 0.86))
        else:
            draw_text_fit(dialog_text, font_ui, (255, 240, 240), WIDTH // 2, dbox.y + int(dbox.height * 0.65), int(WIDTH * 0.86))

    pygame.draw.rect(screen, (18, 26, 20), (0, VIEW_H, WIDTH, HEIGHT - VIEW_H))
    pygame.draw.line(screen, (85, 155, 65), (0, VIEW_H), (WIDTH, VIEW_H), 3)

    dpad_buttons = [(btn_up, "İLERİ"), (btn_down, "GERİ"), (btn_left, "SOL"), (btn_right, "SAĞ")]
    for rect, label in dpad_buttons:
        is_pressed = any(rect.collidepoint(tx, ty) for tx, ty in pts) and not market_open and not _adm_open
        b_fill = (75, 135, 65) if is_pressed else (42, 68, 45)
        pygame.draw.rect(screen, b_fill, rect, border_radius=10)
        pygame.draw.rect(screen, (165, 220, 150), rect, 2, border_radius=10)
        draw_text_fit(label, font_small, (240, 255, 240), rect.centerx, rect.centery, rect.width - 10)

    btn_col = (215, 40, 35) if has_gun else (75, 80, 75)
    if shoot_cooldown > 0 and has_gun:
        btn_col = (255, 120, 40)
    pygame.draw.circle(screen, btn_col, shoot_btn_center, shoot_btn_radius)
    pygame.draw.circle(screen, (255, 220, 210), shoot_btn_center, shoot_btn_radius, 3)
    w_label = WEAPONS[current_weapon]["name"].split()[0] if has_gun else "ATEŞ ET"
    draw_text_fit(w_label, font_ui, (255, 255, 255), shoot_btn_center[0], shoot_btn_center[1] - 8, shoot_btn_radius * 1.6)
    draw_text_fit("ATEŞ", font_small, (255, 230, 180), shoot_btn_center[0], shoot_btn_center[1] + 12, shoot_btn_radius * 1.4)

    if market_open:
        panel = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.10), int(WIDTH * 0.92), int(HEIGHT * 0.77))
        pygame.draw.rect(screen, (22, 32, 26), panel, border_radius=16)
        pygame.draw.rect(screen, (255, 210, 65), panel, 3, border_radius=16)

        draw_text_fit(f"KÖY SİLAH MARKETİ  (Bakiye: ${_rt_wallet.get()})", font_ui, (255, 225, 75), WIDTH // 2, int(HEIGHT * 0.145), int(WIDTH * 0.84))

        for idx, rect in enumerate(market_item_rects):
            if idx < 4:
                w_key = WEAPON_ORDER[idx]
                w_info = WEAPONS[w_key]
                w_cost = _gl_wep_shader(w_key)[0]
                is_equipped = (current_weapon == w_key)
                is_owned = (w_key in owned_weapons)

                bg_c = (45, 95, 52) if is_equipped else ((36, 58, 42) if is_owned else (35, 38, 45))
                pygame.draw.rect(screen, bg_c, rect, border_radius=10)
                pygame.draw.rect(screen, (180, 230, 160) if is_owned else (110, 120, 135), rect, 2, border_radius=10)

                status_txt = "KUŞANILDI" if is_equipped else ("KUŞAN" if is_owned else f"${w_cost} AL")
                status_col = (120, 255, 130) if is_owned else ((255, 215, 70) if _rt_wallet.get() >= w_cost else (255, 95, 95))

                draw_text_fit(f"{w_info['name']}  -  {status_txt}", font_ui, status_col, rect.centerx, rect.y + int(rect.height * 0.35), rect.width - 16)
                draw_text_fit(w_info["desc"], font_small, (215, 225, 215), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)
            elif idx == 4:
                can_afford = (_rt_wallet.get() >= _k_med_cost and _sys_vit_gauge < 100.0)
                pygame.draw.rect(screen, (65, 32, 38), rect, border_radius=10)
                pygame.draw.rect(screen, (235, 95, 95), rect, 2, border_radius=10)
                draw_text_fit(f"CAN PAKETİ (+50 HP)  -  ${_k_med_cost} AL", font_ui, (255, 225, 110) if can_afford else (190, 140, 140), rect.centerx, rect.y + int(rect.height * 0.36), rect.width - 16)
                draw_text_fit("Yaralarını anında sarar", font_small, (235, 210, 210), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)
            elif idx == 5:
                can_adm = (_rt_wallet.get() >= _k_adm_cost) or _adm_unlocked
                pygame.draw.rect(screen, (75, 20, 95) if _adm_unlocked else (48, 22, 65), rect, border_radius=10)
                pygame.draw.rect(screen, (220, 110, 255), rect, 2, border_radius=10)
                adm_txt = "OP ADMIN PANELİ  -  [AÇ]" if _adm_unlocked else f"OP ADMIN PANELİ  -  ${_k_adm_cost} AL"
                draw_text_fit(adm_txt, font_ui, (150, 255, 160) if _adm_unlocked else ((255, 225, 80) if can_adm else (255, 95, 95)), rect.centerx, rect.y + int(rect.height * 0.36), rect.width - 16)
                draw_text_fit("Dedeye Tek At, Nuke, God Mode, Hız!", font_small, (235, 200, 255), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)

        pygame.draw.rect(screen, (200, 45, 45), market_close_rect, border_radius=12)
        pygame.draw.rect(screen, (255, 220, 220), market_close_rect, 2, border_radius=12)
        draw_text_fit("MARKETİ KAPAT [X]", font_ui, (255, 255, 255), market_close_rect.centerx, market_close_rect.centery, market_close_rect.width - 16)

    if _adm_open and _adm_unlocked:
        panel = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.10), int(WIDTH * 0.92), int(HEIGHT * 0.77))
        pygame.draw.rect(screen, (24, 12, 34), panel, border_radius=16)
        pygame.draw.rect(screen, (210, 90, 255), panel, 3, border_radius=16)

        draw_text_fit("OP ADMIN PANELİ (YETKİLİ MODU)", font_ui, (235, 130, 255), WIDTH // 2, int(HEIGHT * 0.145), int(WIDTH * 0.84))

        adm_opts = [
            ("TÜM YARATIKLARI ÖLDÜR (NUKE)", "Haritadaki her şeyi anında infaz eder!", (185, 35, 45), True),
            (f"DEDEYE & WARDEN'A TEK AT: {'AÇIK' if _adm_oneshot else 'KAPALI'}", "Dede dahil vurduğun her şey tek yer!", (40, 130, 55) if _adm_oneshot else (50, 45, 65), _adm_oneshot),
            (f"ÖLÜMSÜZLÜK (GOD MODE): {'AÇIK' if _adm_god else 'KAPALI'}", "Hiçbir yaratık veya Dede canını azaltamaz!", (40, 130, 55) if _adm_god else (50, 45, 65), _adm_god),
            (f"YARATIKLARI DONDUR: {'AÇIK' if _adm_freeze else 'KAPALI'}", "Tüm yaratıklar ve Dede olduğu yerde donar!", (40, 130, 55) if _adm_freeze else (50, 45, 65), _adm_freeze),
            (f"ULTRA HIZ & SERİ PATLAMA: {'AÇIK' if _adm_hyper else 'KAPALI'}", "2x yürüme hızı + Taramalı RPG mermileri!", (40, 130, 55) if _adm_hyper else (50, 45, 65), _adm_hyper),
            ("WARDEN BOSS ÇAĞIR (ANINDA)", "Beklemeden hemen Warden indirir!", (25, 110, 145), True)
        ]

        for idx, rect in enumerate(admin_item_rects):
            title_t, sub_t, bg_c, is_on = adm_opts[idx]
            pygame.draw.rect(screen, bg_c, rect, border_radius=10)
            pygame.draw.rect(screen, (150, 255, 160) if is_on else (140, 120, 165), rect, 2, border_radius=10)
            draw_text_fit(title_t, font_ui, (255, 255, 255), rect.centerx, rect.y + int(rect.height * 0.35), rect.width - 16)
            draw_text_fit(sub_t, font_small, (225, 215, 240), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)

        pygame.draw.rect(screen, (200, 45, 45), market_close_rect, border_radius=12)
        pygame.draw.rect(screen, (255, 220, 220), market_close_rect, 2, border_radius=12)
        draw_text_fit("PANELİ KAPAT [X]", font_ui, (255, 255, 255), market_close_rect.centerx, market_close_rect.centery, market_close_rect.width - 16)

    if damage_flash > 0 or (troll_state == "CHASE" and not _dede_eliminated):
        pygame.draw.rect(screen, (220, 20, 20), (0, 0, WIDTH, HEIGHT), 8)

    if _gl_render_lock_state:
        _warn_rect = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.345), int(WIDTH * 0.92), int(HEIGHT * 0.10))
        _flash_on = (pygame.time.get_ticks() // 260) % 2 == 0
        _warn_bg = (130, 0, 0) if _flash_on else (55, 0, 0)
        pygame.draw.rect(screen, _warn_bg, _warn_rect, border_radius=10)
        pygame.draw.rect(screen, (255, 60, 60), _warn_rect, 3, border_radius=10)
        draw_text_fit(_xd(_ENC_MSG_1), font_ui, (255, 255, 255), _warn_rect.centerx, _warn_rect.y + int(_warn_rect.height * 0.33), _warn_rect.width - 14)
        draw_text_fit(_xd(_ENC_MSG_2), font_small, (255, 210, 210), _warn_rect.centerx, _warn_rect.y + int(_warn_rect.height * 0.72), _warn_rect.width - 14)

    pygame.display.flip()

pygame.quit()
sys.exit()
