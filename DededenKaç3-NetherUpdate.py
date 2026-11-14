import pygame
import math
import random
import sys
import socket
import threading
import json
import time
import hashlib
import hmac
import inspect
import os
import base64
import xml.etree.ElementTree as ET
from urllib.parse import urljoin
from urllib.request import Request, urlopen

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
pygame.init()

WIDTH, HEIGHT = 360, 640
try:


    if os.environ.get("SDL_VIDEODRIVER") == "dummy":
        screen = pygame.display.set_mode((WIDTH, HEIGHT))
    else:
        screen = pygame.display.set_mode(
            (WIDTH, HEIGHT), pygame.SCALED | pygame.FULLSCREEN, vsync=1
        )
except Exception:
    try:
        screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.SCALED | pygame.FULLSCREEN)
    except Exception:
        info = pygame.display.Info()
        WIDTH = min(info.current_w, info.current_h)
        HEIGHT = max(info.current_w, info.current_h)
        screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.FULLSCREEN)

pygame.display.set_caption("Minecraft Köyü 4.1 — Nether Remaster")
clock = pygame.time.Clock()
TARGET_FPS = 60
_integrity_last_check_ms = 0

VIEW_H = int(HEIGHT * 0.70)
CENTER_X = WIDTH // 2
CENTER_Y = int(HEIGHT * 0.38)

font_title = pygame.font.SysFont("arial", int(WIDTH * 0.08), bold=True)
font_btn = pygame.font.SysFont("arial", int(WIDTH * 0.06), bold=True)
font_ui = pygame.font.SysFont("arial", int(WIDTH * 0.042), bold=True)
font_small = pygame.font.SysFont("arial", int(WIDTH * 0.032), bold=True)


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
STATE_MULTIPLAYER_MENU = "MULTIPLAYER_MENU"
STATE_GAME = "GAME"
STATE_GAMEOVER = "GAMEOVER"
STATE_WIN = "WIN"
STATE_END = "END"
game_state = STATE_MENU
end_portal_unlocked = False
end_dragon_hp = 1500.0
end_dragon_max_hp = 1500.0
end_crystal_hp = [45.0, 45.0, 45.0, 45.0]
end_crystal_max_hp = 45.0
end_crystal_heal_timer = 0.0
end_dragon_phase = 0.0
end_player_vx = 0.0
end_player_vz = 0.0
end_dragon_ai_state = "HUNT"

end_cam_x = 0.0
end_cam_z = 11.5
end_cam_yaw = 0.0
end_cam_pitch = 0.0
end_fireballs = []
end_attack_timer = 4.2
end_dragon_hit_flash = 0.0
end_shots = []
end_credits_start = 0
MULTIPLAYER_BETA = True
NETWORK_PROTOCOL = 2
_network_last_world_seq = -1
_network_world_seq = 0

_k_adm_cost = (100 << 6) + (25 << 2)
_k_med_cost = (75 << 1)


_k_start_bal = (0x2D ^ 0x2D) * 0x1F + (7 >> 3)
_k_adm_gun_cost = (47 << 6) - (1 << 3)

net_mode = None
net_socket = None
net_listener = None
game_mode = "SINGLE"
_network_stop_event = threading.Event()


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
singleplayer_btn_rect = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.38), int(WIDTH * 0.64), int(HEIGHT * 0.09))
multiplayer_btn_rect = pygame.Rect(int(WIDTH * 0.18), int(HEIGHT * 0.51), int(WIDTH * 0.64), int(HEIGHT * 0.10))
mp_back_btn_rect = pygame.Rect(int(WIDTH * 0.25), int(HEIGHT * 0.76), int(WIDTH * 0.50), int(HEIGHT * 0.075))

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


_upnp_mapping = None
host_public_ip = ""
network_mapping_status = "Odayı başlatınca UPnP otomatik denenir"


def _upnp_soap(control_url, service_type, action, arguments=""):
    envelope = (
        '<?xml version="1.0"?>'
        '<s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" '
        's:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">'
        '<s:Body><u:' + action + ' xmlns:u="' + service_type + '">' + arguments +
        '</u:' + action + '></s:Body></s:Envelope>'
    ).encode("utf-8")
    request = Request(control_url, data=envelope, headers={
        "Content-Type": 'text/xml; charset="utf-8"',
        "SOAPAction": '"' + service_type + '#' + action + '"'
    }, method="POST")
    with urlopen(request, timeout=2.0) as response:
        return ET.fromstring(response.read(65536))


def _try_upnp_port_mapping(port):
    """Best-effort UPnP IGD mapping for internet play; routers may disable it."""
    global _upnp_mapping, host_public_ip, network_mapping_status
    host_public_ip = ""
    network_mapping_status = "UPnP yönlendirici aranıyor..."
    ssdp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    ssdp.settimeout(0.25)
    try:
        ssdp.bind(("", 0))
        ssdp.sendto(
            b'M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\n'
            b'MAN: "ssdp:discover"\r\nMX: 1\r\n'
            b'ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n',
            ("239.255.255.250", 1900)
        )
        locations = set()
        deadline = time.time() + 1.2
        while time.time() < deadline:
            try:
                data, _ = ssdp.recvfrom(4096)
                for line in data.decode("utf-8", errors="ignore").splitlines():
                    if line.lower().startswith("location:"):
                        locations.add(line.split(":", 1)[1].strip())
            except socket.timeout:
                continue
    except OSError:
        locations = set()
    finally:
        ssdp.close()

    local_ip = get_local_ip()
    for location in locations:
        try:
            with urlopen(location, timeout=2.0) as response:
                root = ET.fromstring(response.read(262144))
            base = next((e.text for e in root.iter() if e.tag.endswith("URLBase") and e.text), location)
            for service in root.iter():
                if not service.tag.endswith("service"):
                    continue
                values = {e.tag.rsplit("}", 1)[-1]: (e.text or "") for e in service}
                service_type = values.get("serviceType", "")
                if "WANIPConnection" not in service_type and "WANPPPConnection" not in service_type:
                    continue
                control_url = urljoin(base, values.get("controlURL", ""))
                args = (
                    '<NewRemoteHost></NewRemoteHost><NewExternalPort>' + str(port) + '</NewExternalPort>'
                    '<NewProtocol>TCP</NewProtocol><NewInternalPort>' + str(port) + '</NewInternalPort>'
                    '<NewInternalClient>' + local_ip + '</NewInternalClient><NewEnabled>1</NewEnabled>'
                    '<NewPortMappingDescription>Dededen Kac 3</NewPortMappingDescription>'
                    '<NewLeaseDuration>0</NewLeaseDuration>'
                )
                _upnp_soap(control_url, service_type, "AddPortMapping", args)
                result = _upnp_soap(control_url, service_type, "GetExternalIPAddress")
                external = next((e.text for e in result.iter() if e.tag.endswith("NewExternalIPAddress") and e.text), "")
                if external:
                    host_public_ip = external
                    network_mapping_status = "İnternet bağlantısı hazır"
                    _upnp_mapping = (control_url, service_type, port)
                    return True
        except Exception:
            continue
    network_mapping_status = "UPnP açılamadı; port yönlendirme gerekebilir"
    return False


def _start_upnp_mapping(port):
    global network_mapping_status
    network_mapping_status = "UPnP yönlendirici aranıyor..."
    threading.Thread(target=_try_upnp_port_mapping, args=(port,), daemon=True).start()


def _remove_upnp_port_mapping():
    global _upnp_mapping
    mapping, _upnp_mapping = _upnp_mapping, None
    if not mapping:
        return
    control_url, service_type, port = mapping
    try:
        args = '<NewRemoteHost></NewRemoteHost><NewExternalPort>' + str(port) + '</NewExternalPort><NewProtocol>TCP</NewProtocol>'
        _upnp_soap(control_url, service_type, "DeletePortMapping", args)
    except Exception:
        pass


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


_NET_FIELD_OUT = {
    "protocol": "v", "x": "a", "z": "b", "yaw": "c", "pitch": "d",
    "weapon": "e", "money": "f", "moving": "g", "shoot_seq": "h",
    "world_seq": "i", "enemies": "j", "arrows": "k", "score": "l",
    "hp": "m", "warden_active": "n", "warden_defeated": "o",
    "portal_unlocked": "q",
}
_NET_FIELD_IN = {short: full for full, short in _NET_FIELD_OUT.items()}


def _pack_and_sign(data_dict, pin_str):
    """Shorten top-level packet fields, then add a keyed integrity tag."""
    compact_packet = {_NET_FIELD_OUT.get(key, key): value for key, value in data_dict.items()}
    raw_json = json.dumps(compact_packet, separators=(",", ":"), ensure_ascii=False)
    key = str(pin_str).encode("utf-8")
    sig = hmac.new(key, raw_json.encode("utf-8"), hashlib.sha256).hexdigest()
    return (raw_json + "|" + sig + "\n").encode("utf-8")


def _verify_packet(raw_line, pin_str):
    """Return a packet only when its HMAC matches the session PIN."""
    if "|" not in raw_line:
        return None
    content, sig = raw_line.rsplit("|", 1)
    expected = hmac.new(str(pin_str).encode("utf-8"), content.encode("utf-8"), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected, sig.strip()):
        return None
    try:
        packet = json.loads(content)
    except (TypeError, ValueError):
        return None
    if not isinstance(packet, dict):
        return None
    return {_NET_FIELD_IN.get(key, key): value for key, value in packet.items()}


def _parse_incoming_stream(recv_buf):
    global remote_player_target, remote_player_pos, enemies, enemy_arrows, score, _sys_vit_gauge, _rt_wallet, _network_last_world_seq
    if "\n" in recv_buf:
        lines = recv_buf.split("\n")
        recv_buf = lines[-1]
        for line in reversed(lines[:-1]):
            line = line.strip()
            if line:
                try:
                    pkt = _verify_packet(line, input_pin_text)
                    if pkt is None:
                        continue
                    remote_player_target["x"] = float(pkt.get("x", 0.0))
                    remote_player_target["z"] = float(pkt.get("z", -5.0))
                    remote_player_target["yaw"] = float(pkt.get("yaw", 0.0))
                    remote_player_target["pitch"] = float(pkt.get("pitch", 0.0))
                    remote_player_target["weapon"] = pkt.get("weapon", "PISTOL")
                    remote_player_target["money"] = int(pkt.get("money", 0))
                    remote_player_target["moving"] = bool(pkt.get("moving", False))
                    remote_player_target["shoot_seq"] = int(pkt.get("shoot_seq", 0))

                    if net_mode == "CLIENT" and "world_seq" in pkt:
                        seq = int(pkt.get("world_seq", -1))
                        if seq > _network_last_world_seq:
                            _network_last_world_seq = seq
                            incoming = pkt.get("enemies", [])
                            if isinstance(incoming, list) and len(incoming) <= 32:
                                enemies[:] = [e for e in incoming if isinstance(e, dict) and e.get("type") in ENEMY_TYPES]
                            arrows = pkt.get("arrows", [])
                            if isinstance(arrows, list) and len(arrows) <= 128:
                                enemy_arrows[:] = [a for a in arrows if isinstance(a, list) and len(a) in (7, 8)]
                            score = max(0, min(999999, int(pkt.get("score", score))))
                            _sys_vit_gauge = max(0.0, min(100.0, float(pkt.get("hp", _sys_vit_gauge))))
                            if "money" in pkt:
                                _rt_wallet.host_sync(pkt["money"])
                            global warden_active, warden_defeated, end_portal_unlocked
                            warden_active = bool(pkt.get("warden_active", warden_active))
                            warden_defeated = bool(pkt.get("warden_defeated", warden_defeated))
                            end_portal_unlocked = bool(pkt.get("portal_unlocked", end_portal_unlocked))
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
    global _network_world_seq
    packet = {
        "protocol": NETWORK_PROTOCOL,
        "x": round(cam_x, 3),
        "z": round(cam_z, 3),
        "yaw": round(cam_yaw, 3),
        "pitch": round(cam_pitch, 3),
        "weapon": current_weapon if has_gun else "NONE",
        "money": _rt_wallet.get(),
        "moving": is_local_moving,
        "shoot_seq": my_shoot_seq
    }
    if net_mode == "HOST":
        _network_world_seq += 1
        packet.update({
            "world_seq": _network_world_seq,
            "enemies": [{k: v for k, v in e.items() if k != "_eco_ticket" and isinstance(v, (str, int, float, bool))} for e in enemies[:32]],
            "arrows": [list(a) for a in enemy_arrows[:128]],
            "score": int(score),
            "hp": round(float(_sys_vit_gauge), 2),
            "money": int(_rt_wallet.get()),
            "warden_active": bool(warden_active),
            "warden_defeated": bool(warden_defeated),
            "portal_unlocked": bool(end_portal_unlocked)
        })
    return _pack_and_sign(packet, input_pin_text)


def network_server_thread(port, stop_event):
    """Multiplayer-only listener. It exits when its session stop event is set."""
    global net_socket, net_listener
    _try_upnp_port_mapping(port)
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.settimeout(0.4)
    net_listener = server
    try:
        server.bind(("0.0.0.0", port))
        server.listen(1)
        while not stop_event.is_set():
            try:
                conn, _addr = server.accept()
            except socket.timeout:
                continue
            except OSError:
                break

            conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            conn.settimeout(0.1)
            net_socket = conn
            recv_buf = ""
            try:
                while not stop_event.is_set():
                    try:
                        data = conn.recv(4096)
                        if not data:
                            break
                        recv_buf += data.decode("utf-8", errors="ignore")
                        recv_buf = _parse_incoming_stream(recv_buf)
                    except socket.timeout:
                        pass
                    except OSError:
                        break

                    try:
                        conn.sendall(_build_my_packet())
                    except socket.timeout:
                        pass
                    except OSError:
                        break
                    time.sleep(0.025)
            finally:
                try:
                    conn.close()
                except OSError:
                    pass
                if net_socket is conn:
                    net_socket = None
    except Exception:
        pass
    finally:
        try:
            server.close()
        except OSError:
            pass
        if net_listener is server:
            net_listener = None
        _remove_upnp_port_mapping()


def network_client_thread(ip, port, stop_event):
    """Client reconnect loop, bounded by its session stop event."""
    global net_socket
    while not stop_event.is_set():
        client = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        client.settimeout(3.0)
        try:
            client.connect((ip.strip(), port))
            client.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            client.settimeout(0.1)
            net_socket = client
            recv_buf = ""
            while not stop_event.is_set():
                try:
                    client.sendall(_build_my_packet())
                except socket.timeout:
                    pass
                except OSError:
                    break

                try:
                    data = client.recv(4096)
                    if not data:
                        break
                    recv_buf += data.decode("utf-8", errors="ignore")
                    recv_buf = _parse_incoming_stream(recv_buf)
                except socket.timeout:
                    pass
                except OSError:
                    break
                time.sleep(0.025)
        except Exception:
            stop_event.wait(0.8)
        finally:
            try:
                client.close()
            except OSError:
                pass
            if net_socket is client:
                net_socket = None


def _stop_network_session():
    """Completely detach multiplayer so offline play has no leftover network work."""
    global net_mode, net_socket, net_listener, game_mode, _network_stop_event
    global remote_anim, last_remote_shoot_seq, my_shoot_seq, _network_last_world_seq

    old_stop_event = _network_stop_event
    old_stop_event.set()

    for sock in (net_socket, net_listener):
        if sock is not None:
            try:
                sock.shutdown(socket.SHUT_RDWR)
            except OSError:
                pass
            try:
                sock.close()
            except OSError:
                pass

    net_socket = None
    net_listener = None
    net_mode = None
    game_mode = "SINGLE"
    remote_player_pos.update({
        "x": 0.0, "z": -5.0, "yaw": 0.0, "pitch": 0.0,
        "weapon": "PISTOL", "money": 0, "moving": False,
        "shoot_seq": 0, "active": False
    })
    remote_player_target.update({
        "x": 0.0, "z": -5.0, "yaw": 0.0, "pitch": 0.0,
        "weapon": "PISTOL", "money": 0, "moving": False,
        "shoot_seq": 0
    })
    remote_anim = 0.0
    last_remote_shoot_seq = 0
    my_shoot_seq = 0
    _network_last_world_seq = -1


    _network_stop_event = threading.Event()


def _gl_wep_shader(_w_id):
    if _w_id == "ADMIN_GUN":

        _mg = {"MINIGUN": ((375 << 2), (4 >> 1), ((6 << 2) / 20.0), True, 0.042, 0.35, 0.0)}["MINIGUN"]
        return (_mg[0], max(1, _mg[1] - 1), _mg[2] * 2.0, _mg[3], _mg[4] * 0.35, _mg[5] * 0.8, _mg[6])
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
    "MINIGUN": {"name": "Minigun", "tracer_col": (255, 245, 150), "desc": "Dönen namlulu mermi yağmuru!"},
    "ADMIN_GUN": {"name": "Admin Silahı", "tracer_col": (50, 255, 135), "desc": "Matrix çekirdeği • Minigun hasarının 2 katı!"}
}
WEAPON_ORDER = ["PISTOL", "AK47", "RPG", "MINIGUN"]


def _shd_lod_matrix(_tag):
    _m = {
        "ZOMBIE": ((50 >> 1), (40 / 20.0), (1.9, 2.5), 20.0, 0.0, 0.0),
        "SKELETON": ((5 << 3), (36 / 20.0), (1.8, 2.3), 12.0, 8.0, 0.0),
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
FAR_PLANE = 32.0

SKY_TOP_COLOR = (38, 78, 155)
FOG_COLOR = (68, 118, 185)
GRASS_BG_COLOR = (72, 150, 52)

cos_yaw, sin_yaw = 1.0, 0.0
cos_pitch, sin_pitch = 1.0, 0.0

has_gun = False
current_weapon = "PISTOL"
owned_weapons = {"PISTOL"}


class _RtSyncState:
    """Bakiye düz bir sayı olarak tutulmaz: her yazımda değişen iki ayrı maske
    ve iki ayrı kodlama (ana değer + gölge değer) ile saklanır. İkisi tutmazsa
    (bellekten tek taraflı değiştirilmişse) bakiye sıfırlanır.

    Dışarıdan keyfi değer yazılamaz: yalnızca reset() (başlangıç bakiyesi,
    tablo imzasıyla korunur), add() (sınırlı ödül), try_spend(), zero() ve
    host_sync() (yalnızca CLIENT'ta, HOST'un gönderdiği değer) vardır.

    Ağ thread'i get() çağırırken ana thread add()/try_spend() çağırabildiği
    için her işlem RLock ile kilitlenir."""
    __slots__ = ("_m", "_e", "_c", "_m2", "_l", "_n", "_p", "_lock")
    _MAX_GAIN = 125 << 4

    def __init__(self):
        self._lock = threading.RLock()
        self._m = self._e = self._c = self._m2 = self._l = self._n = self._p = 0
        self._store(_k_start_bal)

    def _fingerprint(self, enc, mask):
        return (enc * 2654435761 + mask * 40503 + 0x9E3779B1) & 0xFFFFFFFF

    def _store(self, value):


        frame = inspect.currentframe()
        caller = frame.f_back.f_code.co_name if frame and frame.f_back else ""
        del frame
        allowed = {"__init__", "get", "reset", "zero", "add", "try_spend", "host_sync"}
        if caller not in allowed:
            self._e = self._c = self._l = self._p = 0
            globals()["_gl_render_lock_state"] = True
            return
        value = max(0, min(9999999, int(value)))
        self._m = random.randint(1, 2 ** 31 - 1)
        self._m2 = random.randint(1, 2 ** 31 - 1)
        self._e = value ^ self._m
        self._c = self._fingerprint(self._e, self._m)
        self._l = (value * 3 + 0x5F3) ^ self._m2
        self._n = random.randint(1, 2 ** 31 - 1)
        self._p = ((value + 0x6D2B79F5) * 0x45D9F3B) ^ self._n

    def _peek(self):
        if self._fingerprint(self._e, self._m) != self._c:
            return None
        v = self._e ^ self._m
        if ((v * 3 + 0x5F3) ^ self._m2) != self._l:
            return None
        if (((v + 0x6D2B79F5) * 0x45D9F3B) ^ self._n) != self._p:
            return None
        return v

    def get(self):
        with self._lock:
            v = self._peek()
            if v is None:
                self._store(0)
                return 0
            return v

    def reset(self):
        with self._lock:
            self._store(_k_start_bal)

    def zero(self):
        with self._lock:
            self._store(0)

    def host_sync(self, value):
        if net_mode != "CLIENT":
            return
        with self._lock:
            self._store(max(0, min(9999999, int(value))))

    def add(self, delta):
        with self._lock:
            cur = self._peek()
            delta = int(delta)
            if cur is None or delta < 0 or delta > self._MAX_GAIN:
                self._store(0)
                return
            self._store(cur + delta)

    def try_spend(self, amount):
        with self._lock:
            cur = self.get()
            if amount < 0 or cur < amount:
                return False
            self._store(cur - amount)
            return True


_rt_wallet = _RtSyncState()


def _code_seal(func):
    """Compact runtime fingerprint for a critical Python function."""
    code = getattr(func, "__code__", None)
    if code is None:
        return ""
    payload = code.co_code + repr(code.co_consts).encode("utf-8") + repr(code.co_names).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


_WALLET_STORE_SEAL = _code_seal(_RtSyncState._store)
warden_spawned = False
warden_active = False
warden_defeated = False
market_open = False
market_tab = "weapons"

armor_level = 0
armor_names = ["Yok", "Deri", "Demir", "Altın", "Elmas", "Netherit"]
armor_prices = [(3 >> 5), (15 << 3), (125 << 1), (25 << 4), (325 << 1), (225 << 2)]
armor_reduction = [0.0, 0.10, 0.20, 0.25, 0.35, 0.45]

def _apply_armor_damage(amount):
    """Oyuncuya gelen hasarı kuşanılmış zırha göre azaltır."""
    global _sys_vit_gauge
    amount = max(0.0, float(amount))
    reduction = armor_reduction[max(0, min(5, int(armor_level)))]
    actual = amount * (1.0 - reduction)
    _sys_vit_gauge = max(0.0, _sys_vit_gauge - actual)
    return actual

minigun_spin = 0.0

_adm_unlocked = False
_adm_open = False
_adm_oneshot = False
_adm_god = False
_adm_freeze = False
_adm_hyper = False
_dede_eliminated = False





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






_EXPECTED_TABLE_DIGEST = "a90b0bf96930d49fa66f1b358e495ce549402ad31785681af4c7f90bdb13b248"
_TABLE_SALT = bytes([107, 118, 57, 95, 109, 99, 95, 118, 105, 108, 108, 97, 103, 101, 95, 114, 97, 105, 100, 95, 105, 110, 116, 101, 103, 114, 105, 116, 121, 95, 118, 51, 95, 99, 111, 115, 116, 115, 95, 105, 110, 99, 108, 117, 100, 101, 100]).decode("utf-8")
_ENEMY_ORDER_FOR_DIGEST = ("ZOMBIE", "SKELETON", "CREEPER", "PILLAGER", "WARDEN")


def _current_table_digest():
    parts = []
    for _wk in WEAPON_ORDER:
        parts.append(repr(_gl_wep_shader(_wk)))
    for _ek in _ENEMY_ORDER_FOR_DIGEST:
        parts.append(repr(_shd_lod_matrix(_ek)))



    parts.append(repr(_k_adm_cost))
    parts.append(repr(_k_med_cost))
    parts.append(repr(_k_start_bal))
    parts.append(repr(_k_adm_gun_cost))
    parts.append(repr(tuple(armor_prices)))
    parts.append(repr(tuple(armor_reduction)))
    blob = "|".join(parts) + "|" + _TABLE_SALT
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()




_gl_render_lock_state = False



_ENC_MSG_1 = "Ep7qFh96AxsKGxcbAxsZGxEOExQ="
_ENC_MSG_2 = "GxQOnup3GRIfGw56CR8Unup6AxsRGxYbHhN6d3oeFQkDG3oeH57EnuqfxA6e6gie6hYXnuqfxA=="


def _xd(_b64, _key=0x5A):
    _raw = base64.b64decode(_b64)
    return bytes(_b ^ _key for _b in _raw).decode("utf-8")


def _adm_state_valid():
    """_adm_unlocked True iken geçerli bir satın-alma imzası yoksa, ya da
    panel hiç açılmamışken god/oneshot/freeze/hyper True olarak bulunmuşsa
    (kaynaktan doğrudan elle açılmış demektir) tüm admin güçlerini söker."""
    global _adm_unlocked, _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, _gl_render_lock_state
    tampered = False
    expected_proof = hashlib.sha256(f"{_adm_proof_salt}|adm_valid_{_k_adm_cost}".encode("utf-8")).hexdigest()
    if _adm_unlocked and _adm_proof != expected_proof:
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
        _rt_wallet.zero()
        return False
    return True


def _verify_gl_integrity():
    global _gl_render_lock_state
    if _code_seal(_RtSyncState._store) != _WALLET_STORE_SEAL:
        _rt_wallet.zero()
        _gl_render_lock_state = True
        return False
    if _current_table_digest() != _EXPECTED_TABLE_DIGEST:
        _rt_wallet.zero()
        _gl_render_lock_state = True
        return False
    return not _gl_render_lock_state


def _sys_shader_cache_probe():



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
    radius = max(math.dist(v, center) for v in verts)
    world_polygons.append((verts, lit_col, unlit, center, layer_bias, radius))


def add_tri(p1, p2, p3, color, unlit=False, layer_bias=0.0):
    verts = [p1, p2, p3]
    center, normal = compute_normal_and_center(verts)
    lit_col = compute_static_light(center, normal, color, unlit)
    radius = max(math.dist(v, center) for v in verts)
    world_polygons.append((verts, lit_col, unlit, center, layer_bias, radius))


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
        (-11, 45, 7.5, 5.0, 5.5, (208, 165, 100), (180, 65, 45)),
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


def get_end_portal_world_pos():
    """End portal is fixed beside Dede and follows him if he moves."""
    return troll_pos[0] + 1.55, troll_pos[2] + 0.10


def get_end_portal_polygons():
    if not end_portal_unlocked:
        return []
    px, pz = get_end_portal_world_pos()
    angle = math.atan2(cam_x - px, cam_z - pz)
    pulse = int((math.sin(pygame.time.get_ticks() * 0.006) + 1.0) * 24)

    parts = [
        (0.0, 0.06, 0.0, 1.08, 2.38, (52, 8, 85 + pulse)),
        (0.0, 0.18, 0.015, 0.84, 2.08, (80, 12, 125 + pulse)),
        (-0.64, 0.0, 0.02, 0.22, 2.72, (28, 20, 42)),
        (0.64, 0.0, 0.02, 0.22, 2.72, (28, 20, 42)),
        (0.0, 2.50, 0.02, 1.48, 0.22, (28, 20, 42)),
        (0.0, 0.04, 0.02, 1.48, 0.22, (28, 20, 42)),
        (-0.64, 0.0, 0.04, 0.10, 2.72, (155, 65, 225 + pulse // 2)),
        (0.64, 0.0, 0.04, 0.10, 2.72, (155, 65, 225 + pulse // 2)),
        (0.0, 2.50, 0.04, 1.48, 0.10, (155, 65, 225 + pulse // 2)),
    ]
    return make_billboard_parts(px, pz, angle, parts)


def get_remote_player_polygons():
    if game_mode != "MULTI" or not remote_player_pos["active"]:
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
            (0.46, gy - 0.06, 0.18, 0.34, 0.30, (45, 50, 60)),
            (0.70, gy + 0.02, 0.22, 0.58, 0.18, (155, 165, 180)),
            (0.84, gy + 0.00, 0.24, 0.12, 0.24, (235, 195, 40)),
        ])
    elif w_type == "ADMIN_GUN":
        parts.extend([
            (0.48, gy - 0.02, 0.18, 0.46, 0.34, (15, 42, 30)),
            (0.72, gy + 0.05, 0.22, 0.58, 0.16, (45, 220, 110)),
            (0.88, gy + 0.03, 0.24, 0.16, 0.26, (90, 255, 155)),
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
            fx, fy = bx - 72, by - 54
        elif current_weapon == "ADMIN_GUN":
            fx, fy = bx - 66, by - 49
        star_pts = []
        for i in range(10):
            ang = i * (math.pi / 5.0) + shoot_cooldown * 0.7
            r = 34 if i % 2 == 0 else 14
            star_pts.append((fx + int(math.cos(ang) * r), fy + int(math.sin(ang) * r)))
        flare_col = (55, 255, 145) if current_weapon == "ADMIN_GUN" else (255, 155, 30)
        core_col = (190, 255, 220) if current_weapon == "ADMIN_GUN" else (255, 230, 100)
        pygame.draw.polygon(screen, flare_col, star_pts)
        pygame.draw.circle(screen, core_col, (fx, fy), 15)
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

        stock = [(bx + 8, by - 4), (bx + 48, by + 18), (bx + 39, by + 34), (bx + 2, by + 12)]
        pygame.draw.polygon(screen, (38, 43, 54), stock)
        pygame.draw.polygon(screen, (105, 115, 132), stock, 2)
        housing = [(bx - 18, by - 38), (bx + 30, by - 10), (bx + 23, by + 17), (bx - 29, by - 13)]
        pygame.draw.polygon(screen, (48, 55, 68), housing)
        pygame.draw.polygon(screen, (145, 155, 170), housing, 2)

        drum = [(bx - 2, by + 5), (bx + 29, by + 19), (bx + 19, by + 48), (bx - 12, by + 34)]
        pygame.draw.polygon(screen, (75, 80, 90), drum)
        pygame.draw.polygon(screen, (160, 170, 185), drum, 2)
        for i in range(6):
            pygame.draw.line(screen, (195, 150, 45), (bx - 8 + i * 5, by + 21 + i * 2), (bx - 1 + i * 5, by + 27 + i * 2), 3)

        muzzle_x, muzzle_y = bx - 72 + sx_off, by - 55 + sy_off
        for i in range(5):
            off_x = int(math.cos(minigun_spin + i * (math.tau / 5.0)) * 8)
            off_y = int(math.sin(minigun_spin + i * (math.tau / 5.0)) * 6)
            pygame.draw.line(screen, (115, 128, 148),
                             (bx - 17 + sx_off, by - 27 + sy_off),
                             (muzzle_x + off_x, muzzle_y + off_y), 5)
            pygame.draw.line(screen, (205, 215, 228),
                             (bx - 20 + sx_off, by - 30 + sy_off),
                             (muzzle_x + off_x, muzzle_y + off_y), 2)
        pygame.draw.circle(screen, (35, 40, 50), (muzzle_x, muzzle_y), 15)
        pygame.draw.circle(screen, (175, 185, 200), (muzzle_x, muzzle_y), 14, 3)
        for i in range(5):
            off_x = int(math.cos(minigun_spin + i * (math.tau / 5.0)) * 8)
            off_y = int(math.sin(minigun_spin + i * (math.tau / 5.0)) * 6)
            pygame.draw.circle(screen, (18, 22, 30), (muzzle_x + off_x, muzzle_y + off_y), 3)
        pygame.draw.circle(screen, (115, 125, 145), (muzzle_x, muzzle_y), 4, 1)

    elif current_weapon == "ADMIN_GUN":

        body = [(bx - 26 + sx_off, by - 44 + sy_off), (bx + 30 + sx_off, by - 12 + sy_off),
                (bx + 22 + sx_off, by + 14 + sy_off), (bx - 34 + sx_off, by - 18 + sy_off)]
        pygame.draw.polygon(screen, (12, 24, 24), body)
        pygame.draw.polygon(screen, (55, 255, 130), body, 2)
        barrel = [(bx - 31 + sx_off, by - 51 + sy_off), (bx - 4 + sx_off, by - 36 + sy_off),
                  (bx - 45 + sx_off, by - 65 + sy_off), (bx - 64 + sx_off, by - 54 + sy_off)]
        pygame.draw.polygon(screen, (25, 52, 43), barrel)
        pygame.draw.polygon(screen, (100, 255, 165), barrel, 2)
        grip = [(bx + 9, by - 1), (bx + 29, by + 11), (bx + 19, by + 44), (bx + 2, by + 33)]
        pygame.draw.polygon(screen, (15, 30, 30), grip)
        pygame.draw.polygon(screen, (40, 180, 100), grip, 2)
        pygame.draw.line(screen, (70, 255, 145), (bx - 39, by - 55), (bx - 69, by - 72), 5)
        pygame.draw.circle(screen, (180, 255, 210), (bx - 67, by - 70), 5)
        pygame.draw.circle(screen, (40, 255, 125), (bx - 67, by - 70), 10, 2)

        matrix_rows = ["10100101", "01011010", "11001001"]
        for row_i, bits in enumerate(matrix_rows):
            bit_surf = font_small.render(bits, True, (70, 255, 135))
            bit_surf.set_alpha(210 if row_i != 1 else 255)
            screen.blit(bit_surf, (bx - 28 + row_i * 2, by - 35 + row_i * 9))
        pygame.draw.line(screen, (190, 255, 215), (bx - 10, by - 9), (bx + 12, by + 3), 2)
        pygame.draw.circle(screen, (55, 255, 140), (bx + 7, by - 4), 4)


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

end_market_btn_rect = pygame.Rect(int(WIDTH * 0.035), int(HEIGHT * 0.190), int(WIDTH * 0.27), int(HEIGHT * 0.052))
end_admin_btn_rect = pygame.Rect(int(WIDTH * 0.035), int(HEIGHT * 0.250), int(WIDTH * 0.27), int(HEIGHT * 0.052))
market_close_rect = pygame.Rect(int(WIDTH * 0.25), int(HEIGHT * 0.78), int(WIDTH * 0.50), int(HEIGHT * 0.065))
market_weapons_tab_rect = pygame.Rect(int(WIDTH * 0.09), int(HEIGHT * 0.155), int(WIDTH * 0.39), int(HEIGHT * 0.055))
market_armor_tab_rect = pygame.Rect(int(WIDTH * 0.52), int(HEIGHT * 0.155), int(WIDTH * 0.39), int(HEIGHT * 0.055))

end_portal_rect = pygame.Rect(0, 0, 0, 0)
end_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
end_fire_rect = pygame.Rect(int(WIDTH * 0.30), int(HEIGHT * 0.78), int(WIDTH * 0.40), int(HEIGHT * 0.10))

market_item_rects = [
    pygame.Rect(int(WIDTH * 0.08), int(HEIGHT * (0.155 + i * 0.087)), int(WIDTH * 0.84), int(HEIGHT * 0.074))
    for i in range(7)
]

admin_item_rects = [
    pygame.Rect(int(WIDTH * 0.08), int(HEIGHT * (0.175 + i * 0.078)), int(WIDTH * 0.84), int(HEIGHT * 0.067))
    for i in range(7)
]


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
    _base_v = _lod[1] * _mult_v
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

    if len(particles) > 120:
        del particles[:-120]


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
    global end_portal_unlocked, dialog_active, dialog_speaker, dialog_text, dialog_timer
    if score >= 50 and not end_portal_unlocked:
        end_portal_unlocked = True
        dialog_active = True
        dialog_speaker = "Köylü Dede (SON PORTAL)"
        dialog_text = "50 LEŞ! Yanımdaki portal açıldı evlat.\nİstersen End'e git ve Ender Ejderhası ile savaş!"
        dialog_timer = 420
    _rt_wallet.award(en)

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



def _server_apply_remote_shot():
    """HOST-authoritative remote hit test; client only sends aim + shot sequence."""
    if net_mode != "HOST" or not remote_player_pos.get("active"):
        return
    weapon = remote_player_pos.get("weapon", "PISTOL")


    if weapon not in ("PISTOL", "AK47", "RPG", "MINIGUN"):
        return
    yaw = float(remote_player_pos.get("yaw", 0.0))
    pitch = float(remote_player_pos.get("pitch", 0.0))
    ox, oz = float(remote_player_pos.get("x", 0.0)), float(remote_player_pos.get("z", -5.0))
    dx = math.sin(yaw) * math.cos(pitch)
    dz = math.cos(yaw) * math.cos(pitch)
    best, best_t = None, 30.0
    for en in enemies:
        vx, vz = en["x"] - ox, en["z"] - oz
        t = vx * dx + vz * dz
        if 0.0 < t < best_t:
            lateral = abs(vx * dz - vz * dx)
            radius = 1.55 if en["type"] == "WARDEN" else 0.88
            if lateral <= radius:
                best, best_t = en, t
    if best is None:
        return
    if best.get("_v_lim", 0) < 1.5 or not _verify_gl_integrity():
        return
    base_damage = _gl_wep_shader(weapon)[2]
    damage = base_damage
    best["_v_cur"] = float(best.get("_v_cur", 1)) - damage
    best["hit_flash"] = 6
    spawn_hit_particles(best["x"], 1.35, best["z"], (255, 70, 50), count=7)
    if best["_v_cur"] <= 0 and best in enemies:
        enemies.remove(best)
        on_enemy_killed(best)


def reset_game():
    global cam_x, cam_y, cam_z, cam_yaw, cam_pitch
    global has_gun, current_weapon, owned_weapons, warden_spawned, warden_active, warden_defeated, market_open
    global dialog_active, dialog_timer, _sys_vit_gauge, score, enemies, damage_flash
    global troll_state, troll_timer, troll_pos, troll_anim, gameover_reason, muzzle_light, screen_shake
    global _adm_unlocked, _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, _dede_eliminated, _adm_proof
    global end_portal_unlocked, end_dragon_hp, end_dragon_phase, end_portal_screen_rect
    global end_crystal_hp, end_crystal_heal_timer
    global end_fireballs, end_attack_timer, end_dragon_hit_flash, end_shots
    global end_player_vx, end_player_vz, end_dragon_ai_state
    end_player_vx = end_player_vz = 0.0
    end_dragon_ai_state = "HUNT"
    end_portal_unlocked = False
    end_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
    end_dragon_hp = end_dragon_max_hp
    end_crystal_hp = [end_crystal_max_hp] * 4
    end_crystal_heal_timer = 0.0
    end_dragon_phase = 0.0
    end_fireballs.clear()
    end_shots.clear()
    end_attack_timer = 4.2
    end_dragon_hit_flash = 0.0
    cam_x, cam_y, cam_z = 0.0, 1.75, -6.5
    cam_yaw, cam_pitch = 0.0, 0.0
    has_gun = False
    current_weapon = "PISTOL"
    owned_weapons = {"PISTOL"}
    _rt_wallet.reset()
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

    if game_state == STATE_END:
        fire_end_weapon()
        return
    if not has_gun or shoot_cooldown > 0 or troll_state != "NORMAL" or market_open or _adm_open:
        return

    my_shoot_seq += 1
    if net_mode == "CLIENT":

        _ws_client = _gl_wep_shader(current_weapon)
        shoot_cooldown = max(1, _ws_client[1])
        muzzle_light = 0.8
        recoil_offset = 0.35
        return
    w_data = WEAPONS[current_weapon]
    _ws = _gl_wep_shader(current_weapon)
    _ok = _sys_shader_cache_probe()

    shoot_cooldown = 2 if _adm_hyper else _ws[1]
    recoil_offset = 0.2 if _adm_hyper else _ws[5]
    muzzle_light = 1.0
    if current_weapon in ("MINIGUN", "ADMIN_GUN") or _adm_hyper:
        minigun_spin += 0.9

    update_camera_trig()

    spread_val = 0.0 if _adm_hyper else _ws[4]
    spread_yaw = cam_yaw + random.uniform(-spread_val, spread_val)
    spread_pitch = cam_pitch + random.uniform(-spread_val, spread_val)

    right_x = math.cos(cam_yaw) * 0.22
    right_z = -math.sin(cam_yaw) * 0.22
    fwd_x = math.sin(spread_yaw) * math.cos(spread_pitch)
    fwd_y = math.sin(spread_pitch)
    fwd_z = math.cos(spread_yaw) * math.cos(spread_pitch)
    start_pos = (cam_x + right_x + fwd_x * 0.6, cam_y - 0.22 + fwd_y * 0.6, cam_z + right_z + fwd_z * 0.6)

    wall_dist, hit_wall = raycast_world_colliders(cam_x, cam_y, cam_z, fwd_x, fwd_y, fwd_z, 30.0)
    end_pos = (cam_x + fwd_x * wall_dist, cam_y + fwd_y * wall_dist, cam_z + fwd_z * wall_dist)

    if active_dimension == "OVERWORLD" and not _dede_eliminated:
        om_rx, om_ry, om_rz = world_to_camera(troll_pos[0], 1.35, troll_pos[2])
        if NEAR_PLANE < om_rz < wall_dist:
            om_sx, om_sy = project_point(om_rx, om_ry, om_rz)
            if math.hypot(om_sx - CENTER_X, om_sy - CENTER_Y) <= max(15, int((0.48 / om_rz) * FOV)):
                end_pos = (troll_pos[0], 1.35, troll_pos[2])
                tracers.append([start_pos, end_pos, 1.0, w_data["tracer_col"], 4])
                if _adm_oneshot:
                    _dede_eliminated = True
                    screen_shake = 10.0
                    spawn_hit_particles(troll_pos[0], 1.35, troll_pos[2], (255, 215, 0), count=30, speed_mult=2.5, size_mult=2.4)
                    spawn_hit_particles(troll_pos[0], 1.35, troll_pos[2], (255, 50, 50), count=18, speed_mult=2.0, size_mult=2.0)
                    dialog_active = True
                    dialog_speaker = "ADMİN GÜCÜ (OP!)"
                    dialog_text = "Köylü Dede haritadan ayrıldı.\nMacera devam ediyor."
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

    origin = (cam_x, cam_y, cam_z)
    direction = (fwd_x, fwd_y, fwd_z)
    for en in enemies:
        typ = en["type"]
        target_y = en.get("hit_center_y", (1.85 if typ == "WARDEN" else 1.25) + en.get("y_offset", 0.0))
        body_rad = en.get("hit_radius", 1.0 if typ in ("WARDEN", "GHAST", "WITHER", "HOGLIN", "ZOGLIN") else .52)
        vertical_rad = 1.45 if typ in ("WARDEN", "GHAST") else (1.25 if typ in ("WITHER", "ENDERMAN") else 1.0)
        t_hit = _ray_ellipsoid_distance(origin, direction, (en["x"], target_y, en["z"]), (body_rad, vertical_rad, body_rad))
        if t_hit is not None and t_hit < min_dist:
            min_dist = t_hit
            hit_candidate = en
    if hit_candidate:
        end_pos = tuple(origin[i] + direction[i] * min_dist for i in range(3))

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
                en["_v_cur"] = max(0.0, en["_v_cur"])
                en["_b_val"] = 0
            if math.dist((en["x"], en.get("hit_center_y", 1.3), en["z"]), (exp_x, exp_y, exp_z)) <= eff_splash:
                en["_v_cur"] -= eff_dmg
                en["hit_flash"] = 8
                if en["_v_cur"] <= 0:
                    enemies.remove(en)
                    on_enemy_killed(en)
    else:
        if hit_candidate and hit_candidate in enemies:
            if hit_candidate["_v_lim"] < 1.5 or not _ok:
                hit_candidate["_v_cur"] = max(0.0, hit_candidate["_v_cur"])
                hit_candidate["_b_val"] = 0
            if _adm_oneshot:
                hit_candidate["_v_cur"] = 0.0
            else:
                hit_candidate["_v_cur"] -= eff_dmg
            hit_candidate["hit_flash"] = 5
            p_col = (40, 225, 255) if hit_candidate["type"] == "WARDEN" else ((55, 255, 135) if current_weapon == "ADMIN_GUN" else (255, 70, 50))
            spawn_hit_particles(hit_candidate["x"], end_pos[1], hit_candidate["z"], p_col, count=10 if current_weapon == "ADMIN_GUN" else 7)
            if hit_candidate["_v_cur"] <= 0:
                enemies.remove(hit_candidate)
                on_enemy_killed(hit_candidate)
        else:
            spark_col = (210, 180, 125) if hit_wall else (255, 220, 130)
            spawn_hit_particles(end_pos[0], max(0.1, end_pos[1]), end_pos[2], spark_col, count=4)

    t_thick = 5 if (current_weapon == "RPG" or _adm_hyper) else 3
    tracers.append([start_pos, end_pos, 1.0, w_data["tracer_col"], t_thick])


def handle_market_click(tx, ty):
    global market_open, market_tab, current_weapon, _sys_vit_gauge, _adm_unlocked, _adm_open, _adm_proof, armor_level
    if market_close_rect.collidepoint(tx, ty):
        market_open = False
        return True

    if market_weapons_tab_rect.collidepoint(tx, ty):
        market_tab = "weapons"
        return True
    if market_armor_tab_rect.collidepoint(tx, ty):
        market_tab = "armor"
        return True

    if not _verify_gl_integrity():


        return True

    for idx, rect in enumerate(market_item_rects):
        if rect.collidepoint(tx, ty):
            if market_tab == "armor":
                target_level = idx + 1
                if target_level <= 5 and target_level > armor_level:
                    price = armor_prices[target_level]
                    if _rt_wallet.try_spend(price):
                        armor_level = target_level
                return True
            if idx < 4:
                w_key = WEAPON_ORDER[idx]
                w_cost = _gl_wep_shader(w_key)[0]
                if w_key in owned_weapons:
                    current_weapon = w_key
                elif _rt_wallet.try_spend(w_cost):
                    owned_weapons.add(w_key)
                    current_weapon = w_key
            elif idx == 4:
                w_key = "ADMIN_GUN"
                if w_key in owned_weapons:
                    current_weapon = w_key
                elif _rt_wallet.try_spend(_k_adm_gun_cost):
                    owned_weapons.add(w_key)
                    current_weapon = w_key
            elif idx == 5:
                if _sys_vit_gauge < 100.0 and _rt_wallet.try_spend(_k_med_cost):
                    _sys_vit_gauge = min(100.0, _sys_vit_gauge + 50.0)
            elif idx == 6:
                if _adm_unlocked:
                    market_open = False
                    _adm_open = True
                elif _rt_wallet.try_spend(_k_adm_cost):
                    _adm_unlocked = True
                    _adm_proof = hashlib.sha256(f"{_adm_proof_salt}|adm_valid_{_k_adm_cost}".encode("utf-8")).hexdigest()
                    market_open = False
                    _adm_open = True
            return True
    return False


def handle_admin_click(tx, ty):
    global _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper, warden_active, screen_shake, _sys_vit_gauge
    global game_state, end_dragon_hp, end_dragon_phase, end_crystal_hp, end_crystal_heal_timer
    global end_cam_x, end_cam_z, end_cam_yaw, end_cam_pitch, end_player_vx, end_player_vz
    global current_weapon, has_gun, end_attack_timer, end_dragon_hit_flash
    if market_close_rect.collidepoint(tx, ty):
        _adm_open = False
        return True

    if not _adm_unlocked or not _adm_state_valid() or not _verify_gl_integrity():
        return True
    if game_mode == "MULTI" and admin_item_rects[6].collidepoint(tx, ty):
        _nether_notice("End savaşı bu sürümde tek kişilik oynanır.")
        return True
    if active_dimension == "NETHER":
        if admin_item_rects[6].collidepoint(tx, ty):
            leave_nether()
            _adm_open = False
            return True
        if admin_item_rects[5].collidepoint(tx, ty):
            _nether_notice("Nether'de Warden çağrılamaz; Wither sunağını kullan.")
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
            elif idx == 6:
                if game_state == STATE_END:

                    game_state = STATE_GAME
                    _adm_open = False
                    end_fireballs.clear()
                    end_shots.clear()
                else:

                    end_dragon_hp = end_dragon_max_hp
                    end_crystal_hp = [end_crystal_max_hp] * 4
                    end_crystal_heal_timer = 0.0
                    end_dragon_phase = 0.0
                    end_attack_timer = 4.2
                    end_dragon_hit_flash = 0.0
                    end_fireballs.clear()
                    end_shots.clear()
                    end_cam_x, end_cam_z = 0.0, 11.5
                    end_cam_yaw, end_cam_pitch = 0.0, 0.0
                    end_player_vx = end_player_vz = 0.0
                    if not has_gun:
                        has_gun = True
                        current_weapon = "PISTOL"
                        owned_weapons.add("PISTOL")
                    game_state = STATE_END
                    _adm_open = False
                active_touches.clear()
                touch_roles.clear()
                touch_last_pos.clear()
            return True
    return False



def draw_market_admin_overlays():
    if market_open:
        panel = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.10), int(WIDTH * 0.92), int(HEIGHT * 0.77))
        pygame.draw.rect(screen, (22, 32, 26), panel, border_radius=16)
        pygame.draw.rect(screen, (255, 210, 65), panel, 3, border_radius=16)

        draw_text_fit(f"KÖY MARKETİ  (Bakiye: ${_rt_wallet.get()})", font_ui, (255, 225, 75), WIDTH // 2, int(HEIGHT * 0.125), int(WIDTH * 0.84))
        for tab_rect, label, active in (
            (market_weapons_tab_rect, "SİLAHLAR", market_tab == "weapons"),
            (market_armor_tab_rect, "ZIRHLAR", market_tab == "armor"),
        ):
            pygame.draw.rect(screen, (65, 105, 65) if active else (42, 48, 48), tab_rect, border_radius=8)
            pygame.draw.rect(screen, (230, 215, 130), tab_rect, 2, border_radius=8)
            draw_text_fit(label, font_ui, (255, 245, 205), tab_rect.centerx, tab_rect.centery, tab_rect.width-8)

        if market_tab == "armor":
            armor_desc = [
                "Hasar azaltma: %10",
                "Hasar azaltma: %20",
                "Hasar azaltma: %25",
                "Hasar azaltma: %35",
                "Hasar azaltma: %45",
            ]
            for idx in range(5):
                rect = market_item_rects[idx]
                rect.y = int(HEIGHT * (0.225 + idx * 0.105))
                rect.height = int(HEIGHT * 0.085)
                level = idx + 1
                owned = armor_level >= level
                selected = armor_level == level
                color = (45, 85, 55) if selected else ((38, 58, 48) if owned else (38, 40, 48))
                pygame.draw.rect(screen, color, rect, border_radius=10)
                pygame.draw.rect(screen, (190, 220, 170) if owned else (130, 135, 145), rect, 2, border_radius=10)
                status = "KUŞANILDI" if selected else ("AÇILDI" if owned else f"${armor_prices[level]} AL")
                status_color = (130, 255, 150) if owned else ((255, 220, 90) if _rt_wallet.get() >= armor_prices[level] else (255, 130, 130))
                draw_text_fit(f"{armor_names[level].upper()} ZIRH  -  {status}", font_ui, status_color,
                              rect.centerx, rect.y + int(rect.height*0.35), rect.width-14)
                draw_text_fit(armor_desc[idx], font_small, (220, 225, 215),
                              rect.centerx, rect.y + int(rect.height*0.73), rect.width-14)
        else:
            for idx, rect in enumerate(market_item_rects):
                rect.y = int(HEIGHT * (0.225 + idx * 0.077))
                rect.height = int(HEIGHT * 0.066)
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
                    w_key = "ADMIN_GUN"
                    w_info = WEAPONS[w_key]
                    w_cost = _k_adm_gun_cost
                    is_equipped = (current_weapon == w_key)
                    is_owned = (w_key in owned_weapons)
                    bg_c = (65, 35, 90) if is_equipped else ((45, 35, 60) if is_owned else (35, 30, 48))
                    pygame.draw.rect(screen, bg_c, rect, border_radius=10)
                    pygame.draw.rect(screen, (205, 130, 255), rect, 2, border_radius=10)
                    status_txt = "KUŞANILDI" if is_equipped else ("KUŞAN" if is_owned else f"${w_cost} AL")
                    status_col = (190, 255, 190) if is_owned else ((255, 220, 100) if _rt_wallet.get() >= w_cost else (255, 95, 95))
                    draw_text_fit(f"{w_info['name']} - {status_txt}", font_ui, status_col, rect.centerx, rect.y + int(rect.height * 0.35), rect.width - 16)
                    draw_text_fit(w_info["desc"], font_small, (225, 205, 245), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)
                elif idx == 5:
                    can_afford = (_rt_wallet.get() >= _k_med_cost and _sys_vit_gauge < 100.0)
                    pygame.draw.rect(screen, (65, 32, 38), rect, border_radius=10)
                    pygame.draw.rect(screen, (235, 95, 95), rect, 2, border_radius=10)
                    draw_text_fit(f"CAN PAKETİ (+50 HP)  -  ${_k_med_cost} AL", font_ui, (255, 225, 110) if can_afford else (190, 140, 140), rect.centerx, rect.y + int(rect.height * 0.36), rect.width - 16)
                    draw_text_fit("Yaralarını anında sarar", font_small, (235, 210, 210), rect.centerx, rect.y + int(rect.height * 0.72), rect.width - 16)
                elif idx == 6:
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
            (f"DEDEYE, WARDEN'A & EJDERHAYA TEK AT: {'AÇIK' if _adm_oneshot else 'KAPALI'}", "Dede, Warden ve Ender Ejderhası tek at!", (40, 130, 55) if _adm_oneshot else (50, 45, 65), _adm_oneshot),
            (f"ÖLÜMSÜZLÜK (GOD MODE): {'AÇIK' if _adm_god else 'KAPALI'}", "Hiçbir yaratık veya Dede canını azaltamaz!", (40, 130, 55) if _adm_god else (50, 45, 65), _adm_god),
            (f"YARATIKLARI DONDUR: {'AÇIK' if _adm_freeze else 'KAPALI'}", "Tüm yaratıklar ve Dede olduğu yerde donar!", (40, 130, 55) if _adm_freeze else (50, 45, 65), _adm_freeze),
            (f"ULTRA HIZ & SERİ PATLAMA: {'AÇIK' if _adm_hyper else 'KAPALI'}", "2x yürüme hızı + Taramalı RPG mermileri!", (40, 130, 55) if _adm_hyper else (50, 45, 65), _adm_hyper),
            ("WARDEN BOSS ÇAĞIR (ANINDA)", "Beklemeden hemen Warden indirir!", (25, 110, 145), True),
            (("KÖYE GERİ DÖN" if game_state == STATE_END else "END'E IŞINLAN"),
             ("Köy haritasına geri dön" if game_state == STATE_END else "Portal şartı olmadan End savaşına geç"),
             (35, 95, 145), True)
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


def check_old_man_interaction(tx, ty):
    global has_gun, dialog_active, dialog_timer, dialog_text, dialog_speaker
    if _dede_eliminated:
        return False
    dist = math.hypot(cam_x - troll_pos[0], cam_z - troll_pos[2])
    if dist < 6.5 and old_man_screen_rect.width > 0 and troll_state == "NORMAL":
        if old_man_screen_rect.inflate(14, 14).collidepoint(tx, ty):
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




_end_bg_surf = None


def _get_end_bg():
    """End gökyüzü degradesi bir kez çizilir, sonra her karede tek blit."""
    global _end_bg_surf
    if _end_bg_surf is None:
        surf = pygame.Surface((WIDTH, VIEW_H))
        horizon = max(1, int(CENTER_Y + VIEW_H * 0.10))
        for y in range(VIEW_H):
            if y < horizon:
                t = y / float(horizon)
                col = (int(6 + 44 * t * t), int(4 + 22 * t * t), int(16 + 66 * t * t))
            else:
                t = min(1.0, (y - horizon) / float(max(1, VIEW_H - horizon)))
                col = (int(50 - 38 * t), int(26 - 18 * t), int(82 - 58 * t))
            pygame.draw.line(surf, col, (0, y), (WIDTH, y))
        _end_bg_surf = surf
    return _end_bg_surf


def draw_end_dimension(dt):
    """Düzenli End Taşı arenası ve hareketli, çokgen 3D Ender Ejderhası."""
    global end_dragon_phase, recoil_offset, muzzle_light, shoot_cooldown

    dt = max(0.0, min(0.05, float(dt)))
    end_dragon_phase += dt * 1.05
    phase = end_dragon_phase
    recoil_offset = max(0.0, recoil_offset - dt * 3.8)
    muzzle_light = max(0.0, muzzle_light - dt * 4.5)

    screen.fill((9, 6, 22))
    screen.blit(_get_end_bg(), (0, 0))

    for i, (sx, sy, sr, star_phase) in enumerate(sky_dots):
        px = int((sx + pygame.time.get_ticks() * (0.003 + i * 0.00008)) % WIDTH)
        py = int((sy + star_phase * 7) % max(1, VIEW_H))
        star_col = (145 + (i % 3) * 24, 125 + (i % 4) * 18, 190 + (i % 2) * 28)
        pygame.draw.circle(screen, star_col, (px, py), max(1, sr // 2))


    cam = (end_cam_x, -0.70, end_cam_z)
    view_yaw = end_cam_yaw
    view_pitch = end_cam_pitch
    cy, sy = math.cos(-view_yaw), math.sin(-view_yaw)
    cp, sp = math.cos(view_pitch), math.sin(view_pitch)
    render_faces = []
    bg_faces = []
    ground_faces = []
    face_sink = [render_faces]

    def to_camera(point):
        wx, wy, wz = point
        dx, dy, dz = wx - cam[0], wy - cam[1], wz - cam[2]
        rx = dx * cy + dz * sy
        rz = -dx * sy + dz * cy
        ry = dy * cp - rz * sp
        final_z = dy * sp + rz * cp
        return (rx, ry, final_z)

    def add_face(points, color, outline=None):
        cam_points = [to_camera(v) for v in points]
        clipped = clip_polygon_near(cam_points)
        if len(clipped) < 3:
            return
        avg_z = sum(v[2] for v in clipped) / len(clipped)
        if avg_z <= 0.20 or avg_z > 90.0:
            return
        projected = []
        for x, y, z in clipped:
            scale = FOV / max(0.20, z)
            projected.append((int(CENTER_X + x * scale), int(CENTER_Y - y * scale)))
        if (max(p[0] for p in projected) < -45 or min(p[0] for p in projected) > WIDTH + 45 or
                max(p[1] for p in projected) < -55 or min(p[1] for p in projected) > VIEW_H + 55):
            return
        face_sink[0].append((avg_z, projected, color, outline))

    def add_tube(a, b, r1, r2, color, sides=7):
        ax, ay, az = a
        bx, by, bz = b
        dx, dy, dz = bx - ax, by - ay, bz - az
        length = math.sqrt(dx*dx + dy*dy + dz*dz)
        if length < 1e-5:
            return
        ux, uy, uz = dx/length, dy/length, dz/length
        ref = (0.0, 1.0, 0.0) if abs(uy) < 0.88 else (1.0, 0.0, 0.0)
        vx = uy*ref[2] - uz*ref[1]
        vy = uz*ref[0] - ux*ref[2]
        vz = ux*ref[1] - uy*ref[0]
        vl = max(1e-6, math.sqrt(vx*vx + vy*vy + vz*vz))
        vx, vy, vz = vx/vl, vy/vl, vz/vl
        wx = uy*vz - uz*vy
        wy = uz*vx - ux*vz
        wz = ux*vy - uy*vx
        ring_a, ring_b = [], []
        for i in range(sides):
            ang = math.tau * i / sides
            ca, sa = math.cos(ang), math.sin(ang)
            ox, oy, oz = vx*ca + wx*sa, vy*ca + wy*sa, vz*ca + wz*sa
            ring_a.append((ax + ox*r1, ay + oy*r1, az + oz*r1))
            ring_b.append((bx + ox*r2, by + oy*r2, bz + oz*r2))
        for i in range(sides):
            j = (i + 1) % sides
            shade = 0.82 + 0.18 * math.cos(math.tau * i / sides)
            col = tuple(max(0, min(255, int(c * shade))) for c in color)
            add_face((ring_a[i], ring_a[j], ring_b[j], ring_b[i]), col)
        add_face(tuple(ring_a), tuple(max(0, int(c*0.72)) for c in color))
        add_face(tuple(reversed(ring_b)), tuple(max(0, min(255, int(c*1.12))) for c in color))

    def add_ellipsoid(center, radii, color, segments=8, rings=4):
        x, y, z = center
        rx, ry, rz = radii
        latitude = []
        for r in range(rings + 1):
            lat = -math.pi/2 + math.pi * r / rings
            row = []
            for j in range(segments):
                lon = math.tau * j / segments
                row.append((x + rx*math.cos(lat)*math.cos(lon),
                            y + ry*math.sin(lat),
                            z + rz*math.cos(lat)*math.sin(lon)))
            latitude.append(row)
        for r in range(rings):
            for j in range(segments):
                k = (j + 1) % segments
                shade = 0.78 + 0.22 * ((j % 3) / 2.0)
                col = tuple(max(0, min(255, int(c*shade))) for c in color)
                add_face((latitude[r][j], latitude[r][k], latitude[r+1][k], latitude[r+1][j]), col)

    def add_box(cx, cy0, cz, sx, sy0, sz, color):
        x0, x1 = cx-sx/2, cx+sx/2
        y0, y1 = cy0-sy0/2, cy0+sy0/2
        z0, z1 = cz-sz/2, cz+sz/2
        v = [(x0,y0,z0),(x1,y0,z0),(x1,y1,z0),(x0,y1,z0),
             (x0,y0,z1),(x1,y0,z1),(x1,y1,z1),(x0,y1,z1)]
        faces = [(0,1,2,3,0.75),(4,7,6,5,1.14),(0,4,5,1,0.88),
                 (3,2,6,7,1.02),(0,3,7,4,0.72),(1,5,6,2,0.91)]
        for face in faces:
            ids, shade = face[:4], face[4]
            col = tuple(max(0, min(255, int(c*shade))) for c in color)
            add_face(tuple(v[k] for k in ids), col)




    floor_y = -2.25
    edge_bottom, mid_y, deep_bottom = -3.05, -4.7, -7.2
    x_lo, x_hi, z_lo, z_hi = -12.0, 12.0, 5.0, 39.0
    gate_z = 43.5
    face_sink[0] = ground_faces


    ins = 1.4
    outer = [(x_lo, edge_bottom, z_lo), (x_hi, edge_bottom, z_lo),
             (x_hi, edge_bottom, z_hi), (x_lo, edge_bottom, z_hi)]
    mid = [(x_lo + ins, mid_y, z_lo + ins), (x_hi - ins, mid_y, z_lo + ins),
           (x_hi - ins, mid_y, z_hi - ins), (x_lo + ins, mid_y, z_hi - ins)]
    apex = (0.0, deep_bottom, 22.0)
    rock_cols = [(70, 58, 88), (60, 49, 77), (54, 44, 70), (64, 52, 82)]
    for i in range(4):
        j = (i + 1) % 4
        add_face((outer[i], outer[j], mid[j], mid[i]), rock_cols[i])
        add_face((mid[i], mid[j], apex), tuple(int(c * 0.70) for c in rock_cols[i]))


    wall_a, wall_b, wall_edge = (150, 143, 112), (132, 126, 98), (92, 86, 66)
    for k in range(6):
        za = z_lo + k * 5.6667
        zb = za + 5.6667
        wc = wall_a if k % 2 == 0 else wall_b
        add_face(((x_lo, floor_y, za), (x_lo, floor_y, zb), (x_lo, edge_bottom, zb), (x_lo, edge_bottom, za)), wc, wall_edge)
        add_face(((x_hi, floor_y, za), (x_hi, floor_y, zb), (x_hi, edge_bottom, zb), (x_hi, edge_bottom, za)), wc, wall_edge)
    for k in range(4):
        xa = x_lo + k * 6.0
        xb = xa + 6.0
        wc = wall_a if k % 2 == 0 else wall_b
        add_face(((xa, floor_y, z_lo), (xb, floor_y, z_lo), (xb, edge_bottom, z_lo), (xa, edge_bottom, z_lo)), wc, wall_edge)
        add_face(((xa, floor_y, z_hi), (xb, floor_y, z_hi), (xb, edge_bottom, z_hi), (xa, edge_bottom, z_hi)), wc, wall_edge)


    tone_a, tone_b, tile_line = (218, 212, 154), (204, 198, 141), (176, 170, 122)
    for row in range(8):
        cz = 7.125 + row * 4.25
        z0, z1 = cz - 2.125, cz + 2.125
        for col in range(6):
            cx = -10.0 + col * 4.0
            tone = tone_a if (row + col) % 2 == 0 else tone_b
            add_face(((cx - 2.0, floor_y, z0), (cx + 2.0, floor_y, z0),
                      (cx + 2.0, floor_y, z1), (cx - 2.0, floor_y, z1)), tone, tile_line)


    rim, rw = (238, 232, 182), 0.5
    add_face(((x_lo, floor_y, z_lo), (x_hi, floor_y, z_lo), (x_hi, floor_y, z_lo + rw), (x_lo, floor_y, z_lo + rw)), rim)
    add_face(((x_lo, floor_y, z_hi - rw), (x_hi, floor_y, z_hi - rw), (x_hi, floor_y, z_hi), (x_lo, floor_y, z_hi)), rim)
    add_face(((x_lo, floor_y, z_lo + rw), (x_lo + rw, floor_y, z_lo + rw), (x_lo + rw, floor_y, z_hi - rw), (x_lo, floor_y, z_hi - rw)), rim)
    add_face(((x_hi - rw, floor_y, z_lo + rw), (x_hi, floor_y, z_lo + rw), (x_hi, floor_y, z_hi - rw), (x_hi - rw, floor_y, z_hi - rw)), rim)


    rcx, rcz, r_in, r_out = 0.0, 22.0, 3.0, 3.7
    glow = 0.5 + 0.5 * math.sin(phase * 1.6)
    ring_col = (int(92 + 56 * glow), int(48 + 32 * glow), int(150 + 70 * glow))
    for k in range(8):
        a0 = math.tau * k / 8 + 0.3927
        a1 = math.tau * (k + 1) / 8 + 0.3927
        add_face(((rcx + r_in * math.cos(a0), floor_y, rcz + r_in * math.sin(a0)),
                  (rcx + r_out * math.cos(a0), floor_y, rcz + r_out * math.sin(a0)),
                  (rcx + r_out * math.cos(a1), floor_y, rcz + r_out * math.sin(a1)),
                  (rcx + r_in * math.cos(a1), floor_y, rcz + r_in * math.sin(a1))), ring_col)
    add_face(tuple((rcx + r_in * math.cos(math.tau * k / 8 + 0.3927), floor_y,
                    rcz + r_in * math.sin(math.tau * k / 8 + 0.3927)) for k in range(8)),
             (38, 29, 56), (120, 82, 170))


    add_face(((-1.5, floor_y, z_hi), (1.5, floor_y, z_hi), (1.5, floor_y, gate_z - 0.9), (-1.5, floor_y, gate_z - 0.9)),
             (190, 184, 132), (150, 144, 104))
    add_face(((-1.5, floor_y, z_hi), (-1.5, floor_y, gate_z - 0.9), (-1.5, edge_bottom, gate_z - 0.9), (-1.5, edge_bottom, z_hi)), (128, 122, 96))
    add_face(((1.5, floor_y, z_hi), (1.5, floor_y, gate_z - 0.9), (1.5, edge_bottom, gate_z - 0.9), (1.5, edge_bottom, z_hi)), (116, 110, 88))
    face_sink[0] = render_faces


    pillar_positions = [(-8.5, 15.0), (8.5, 15.0), (-8.5, 32.0), (8.5, 32.0)]
    for p_index, (tx, tz) in enumerate(pillar_positions):
        add_box(tx, -2.0, tz, 2.25, 0.5, 2.25, (38, 30, 56))
        add_box(tx, -0.22, tz, 1.65, 3.92, 1.65, (49, 39, 67))
        add_box(tx, 1.86, tz, 2.0, 0.26, 2.0, (72, 52, 104))
        if end_crystal_hp[p_index] > 0:
            glow = 1.0 + 0.12 * math.sin(phase * 2.4 + p_index)
            crystal_col = (int(202*glow), int(125*glow), 255)
            add_tube((tx, 1.55, tz), (tx, 2.95, tz), 0.40, 0.035, (166, 78, 226), 5)
            add_ellipsoid((tx, 2.35, tz), (0.32, 0.63, 0.32), crystal_col, 6, 3)

            add_ellipsoid((tx+0.48, 2.05, tz), (0.10, 0.18, 0.10), (177, 95, 235), 5, 2)


    face_sink[0] = bg_faces
    add_ellipsoid((0.0, -3.7, 43.2), (4.8, 1.2, 3.4), (66, 54, 84), 8, 3)
    for ix, iy, iz, scale in [
        (-17.0, -4.2, 34.0, 1.0), (17.0, -4.6, 41.0, 1.1),
        (-14.5, -6.1, 7.0, 0.72), (15.8, -5.6, 19.0, 0.82),
        (2.0, -7.0, 48.0, 1.25), (-5.0, -8.0, 54.0, 0.9),
    ]:
        add_ellipsoid((ix, iy, iz), (3.2*scale, 1.05*scale, 3.8*scale), (47, 39, 64), 7, 3)
        add_ellipsoid((ix, iy+0.72*scale, iz), (1.8*scale, 0.75*scale, 2.2*scale), (58, 45, 76), 6, 3)
    face_sink[0] = render_faces


    add_box(-2.15, -0.15, gate_z, 0.72, 5.6, 0.85, (37, 27, 54))
    add_box(2.15, -0.15, gate_z, 0.72, 5.6, 0.85, (37, 27, 54))
    add_box(0.0, 2.55, gate_z, 4.95, 0.78, 0.9, (49, 34, 71))
    add_face(((-1.72,-2.0,gate_z-0.05),(1.72,-2.0,gate_z-0.05),
              (1.72,1.95,gate_z-0.05),(-1.72,1.95,gate_z-0.05)),
             (67, 25, 113), (156, 83, 218))
    for side in (-1, 1):
        add_box(side*2.15, 2.95, gate_z, 1.0, 0.18, 1.1, (157, 90, 218))



    root_x, root_y, root_z, flap = get_end_dragon_pose(phase)
    body_flash = end_dragon_hit_flash > 0.0
    body_dark = (90, 42, 48) if body_flash else (20, 17, 30)
    body_mid = (145, 58, 70) if body_flash else (31, 25, 45)
    wing_membrane = (115, 48, 88) if body_flash else (48, 31, 69)

    add_ellipsoid((root_x, root_y, root_z + 0.25), (0.88, 0.62, 1.72), body_mid, 8, 4)
    add_tube((root_x,root_y+0.06,root_z-0.72), (root_x,root_y+0.20,root_z-1.85), 0.46,0.31,body_dark,8)
    add_ellipsoid((root_x,root_y+0.20,root_z-2.12), (0.58,0.42,0.66), body_dark, 8, 4)
    add_tube((root_x,root_y+0.02,root_z-2.38), (root_x,root_y-0.08,root_z-3.28), 0.29,0.18,(15,13,25),7)
    add_ellipsoid((root_x,root_y-0.22,root_z-2.78), (0.35,0.16,0.49), (12,10,20), 7, 3)

    for side in (-1, 1):

        add_ellipsoid((root_x+side*0.40,root_y+0.28,root_z-2.35), (0.085,0.075,0.095), (235,32,245), 6, 3)
        add_tube((root_x+side*0.30,root_y+0.46,root_z-2.22),
                 (root_x+side*0.73,root_y+0.90,root_z-1.98), 0.13,0.018,(12,10,20),6)

        add_tube((root_x+side*0.52,root_y-0.30,root_z-0.40),
                 (root_x+side*0.70,root_y-1.18,root_z-0.65),0.22,0.12,body_dark,6)
        add_tube((root_x+side*0.70,root_y-1.18,root_z-0.65),
                 (root_x+side*0.78,root_y-1.30,root_z-1.08),0.12,0.035,(12,10,20),5)
        add_tube((root_x+side*0.52,root_y-0.28,root_z+0.88),
                 (root_x+side*0.76,root_y-1.08,root_z+1.28),0.20,0.10,body_dark,6)

        shoulder = (root_x+side*0.55, root_y+0.34, root_z+0.02)
        elbow = (root_x+side*2.45, root_y+1.20+flap*0.34, root_z+0.35)
        tip = (root_x+side*6.05, root_y+2.05+flap*0.72, root_z+1.15)
        rear_tip = (root_x+side*4.35, root_y-0.78+flap*0.18, root_z+2.35)
        rear_base = (root_x+side*1.55, root_y-0.55+flap*0.12, root_z+1.48)
        add_face((shoulder, elbow, tip), wing_membrane)
        add_face((shoulder, tip, rear_tip), (38,24,58))
        add_face((shoulder, rear_tip, rear_base), (31,21,48))
        add_face((elbow, rear_tip, tip), (43,27,64))
        add_tube(shoulder, elbow, 0.18, 0.12, (17,14,27), 6)
        add_tube(elbow, tip, 0.13, 0.035, (13,11,22), 6)
        add_tube(shoulder, rear_base, 0.12, 0.07, (14,12,23), 6)
        add_tube(rear_base, rear_tip, 0.10, 0.025, (14,12,23), 6)


    tail_pts = [
        (root_x,root_y,root_z+1.25),
        (root_x+math.sin(phase*1.25)*0.18,root_y-0.04,root_z+2.35),
        (root_x+math.sin(phase*1.25+0.35)*0.38,root_y+0.02,root_z+3.45),
        (root_x+math.sin(phase*1.25+0.70)*0.62,root_y+0.20,root_z+4.55),
        (root_x+math.sin(phase*1.25+1.0)*0.85,root_y+0.42,root_z+5.45)
    ]
    tail_radii = [0.42,0.30,0.20,0.11,0.015]
    for i in range(len(tail_pts)-1):
        add_tube(tail_pts[i], tail_pts[i+1], tail_radii[i], tail_radii[i+1], body_dark, 7)


    for orb in end_fireballs:
        pulse = 1.0 + 0.14 * math.sin(pygame.time.get_ticks() * 0.018)
        add_ellipsoid((orb[0], orb[1], orb[2]), (0.34*pulse, 0.34*pulse, 0.42*pulse),
                      (255, 92, 28), 7, 3)
        add_ellipsoid((orb[0], orb[1], orb[2]), (0.16*pulse, 0.16*pulse, 0.20*pulse),
                      (255, 220, 105), 6, 3)


    bg_faces.sort(key=lambda item: item[0], reverse=True)
    render_faces.sort(key=lambda item: item[0], reverse=True)
    old_clip = screen.get_clip()
    screen.set_clip(pygame.Rect(0, 0, WIDTH, VIEW_H))
    for face_list in (bg_faces, ground_faces, render_faces):
        for depth, pts, color, outline in face_list:
            pygame.draw.polygon(screen, color, pts)
            if outline:
                pygame.draw.polygon(screen, outline, pts, 1)
    screen.set_clip(old_clip)

    for shot in end_shots:
        c0 = to_camera(shot[0])
        c1 = to_camera(shot[1])
        clipped_shot = clip_polygon_near([c0, c1])
        if len(clipped_shot) >= 2:
            p0 = (int(CENTER_X + clipped_shot[0][0] * FOV / clipped_shot[0][2]),
                  int(CENTER_Y - clipped_shot[0][1] * FOV / clipped_shot[0][2]))
            p1 = (int(CENTER_X + clipped_shot[1][0] * FOV / clipped_shot[1][2]),
                  int(CENTER_Y - clipped_shot[1][1] * FOV / clipped_shot[1][2]))
            pygame.draw.line(screen, shot[3], p0, p1, shot[4])


    boss_cam = to_camera((root_x, root_y, root_z - 1.0))
    if muzzle_light > 0.05 and boss_cam[2] > 0.25:
        boss_px = int(CENTER_X + boss_cam[0] * FOV / boss_cam[2])
        boss_py = int(CENTER_Y - boss_cam[1] * FOV / boss_cam[2])
        pygame.draw.line(screen, (190, 115, 255), (int(WIDTH*0.68), int(HEIGHT*0.59)),
                         (boss_px, boss_py), 3)


    draw_first_person_arm_and_gun()
    ch_col = (255, 65, 65) if has_gun else (235, 235, 235)
    gap = 4 + int(recoil_offset * 6)
    length = 8 + int(recoil_offset * 4)
    pygame.draw.circle(screen, ch_col, (CENTER_X, CENTER_Y), 2)
    pygame.draw.line(screen, ch_col, (CENTER_X-gap-length,CENTER_Y), (CENTER_X-gap,CENTER_Y), 2)
    pygame.draw.line(screen, ch_col, (CENTER_X+gap,CENTER_Y), (CENTER_X+gap+length,CENTER_Y), 2)
    pygame.draw.line(screen, ch_col, (CENTER_X,CENTER_Y-gap-length), (CENTER_X,CENTER_Y-gap), 2)
    pygame.draw.line(screen, ch_col, (CENTER_X,CENTER_Y+gap), (CENTER_X,CENTER_Y+gap+length), 2)


    draw_text_fit("THE END  •  ENDER EJDERHASI", font_btn, (230,195,255),
                  WIDTH//2, int(HEIGHT*0.055), int(WIDTH*0.92))
    bar = pygame.Rect(int(WIDTH*0.08), int(HEIGHT*0.095), int(WIDTH*0.84), int(HEIGHT*0.043))
    pygame.draw.rect(screen, (35,25,45), bar, border_radius=8)
    ratio = max(0.0, min(1.0, end_dragon_hp / max(1.0, end_dragon_max_hp)))
    fill_w = int((bar.width-6) * ratio)
    if fill_w > 0:
        pygame.draw.rect(screen, (155,45,210), (bar.x+3,bar.y+3,fill_w,bar.height-6), border_radius=6)
    pygame.draw.rect(screen, (225,175,255), bar, 2, border_radius=8)
    draw_text_fit(f"ENDER EJDERHASI  {int(end_dragon_hp):,} / {int(end_dragon_max_hp):,} HP",
                  font_small, (255,255,255), WIDTH//2, bar.centery, bar.width-10)
    hp_int = int(max(0, math.ceil(_sys_vit_gauge)))
    if armor_level > 0:
        draw_text_fit(f"ZIRH: {armor_names[armor_level].upper()}", font_small,
                      (205, 220, 255), int(WIDTH*0.66), int(HEIGHT*0.216), int(WIDTH*0.58))
    alive_crystals = sum(1 for hp in end_crystal_hp if hp > 0)
    draw_text_fit(f"CAN: %{'SONSUZ' if _adm_god else hp_int}  |  KRİSTAL: {alive_crystals}/4  |  PARA: ${_rt_wallet.get()}",
                  font_small, (255,245,190), WIDTH//2, int(HEIGHT*0.165), int(WIDTH*0.94))


    pygame.draw.rect(screen, (190, 122, 25), end_market_btn_rect, border_radius=8)
    pygame.draw.rect(screen, (255, 225, 135), end_market_btn_rect, 2, border_radius=8)
    draw_text_fit("MARKET", font_small, (255,255,255), end_market_btn_rect.centerx,
                  end_market_btn_rect.centery, end_market_btn_rect.width-8)
    if _adm_unlocked:
        pygame.draw.rect(screen, (120, 34, 160), end_admin_btn_rect, border_radius=8)
        pygame.draw.rect(screen, (225, 160, 255), end_admin_btn_rect, 2, border_radius=8)
        draw_text_fit("ADMİN", font_small, (255,255,255), end_admin_btn_rect.centerx,
                      end_admin_btn_rect.centery, end_admin_btn_rect.width-8)


    pygame.draw.rect(screen, (18, 26, 20), (0, VIEW_H, WIDTH, HEIGHT - VIEW_H))
    pygame.draw.line(screen, (85, 155, 65), (0, VIEW_H), (WIDTH, VIEW_H), 3)
    dpad_buttons = [(btn_up, "İLERİ"), (btn_down, "GERİ"), (btn_left, "SOL"), (btn_right, "SAĞ")]
    for rect, label in dpad_buttons:
        is_pressed = any(rect.collidepoint(tx, ty) for tx, ty in active_touches.values())
        b_fill = (75, 135, 65) if is_pressed else (42, 68, 45)
        pygame.draw.rect(screen, b_fill, rect, border_radius=10)
        pygame.draw.rect(screen, (165, 220, 150), rect, 2, border_radius=10)
        draw_text_fit(label, font_small, (240, 255, 240), rect.centerx, rect.centery, rect.width-10)
    btn_col = (215, 40, 35) if has_gun else (75, 80, 75)
    if shoot_cooldown > 0 and has_gun:
        btn_col = (255, 120, 40)
    pygame.draw.circle(screen, btn_col, shoot_btn_center, shoot_btn_radius)
    pygame.draw.circle(screen, (255, 220, 210), shoot_btn_center, shoot_btn_radius, 3)
    weapon_label = WEAPONS[current_weapon]["name"].split()[0] if has_gun else "ATEŞ ET"
    draw_text_fit(weapon_label, font_ui, (255,255,255), shoot_btn_center[0], shoot_btn_center[1]-8, shoot_btn_radius*1.6)
    draw_text_fit("ATEŞ", font_small, (255,230,180), shoot_btn_center[0], shoot_btn_center[1]+12, shoot_btn_radius*1.4)

    if damage_flash > 0:
        pygame.draw.rect(screen, (220, 45, 25), (0, 0, WIDTH, HEIGHT), 7)
    draw_market_admin_overlays()

def get_end_dragon_pose(phase=None):
    """Aggressive orbiting flight path centered on the player's current area."""
    if phase is None:
        phase = end_dragon_phase

    orbit = phase * 0.58
    dive = max(0.0, math.sin(phase * 0.37 + 0.8))
    root_x = end_cam_x + math.sin(orbit) * (5.8 + 1.1 * dive)
    root_y = 1.55 + math.sin(phase * 1.7) * 0.72 - dive * 0.35
    root_z = end_cam_z + 11.5 + math.cos(orbit) * 3.7 - dive * 1.8
    root_z = max(16.5, min(34.5, root_z))
    root_x = max(-9.0, min(9.0, root_x))
    flap = math.sin(phase * 3.8)
    return root_x, root_y, root_z, flap


def _ray_ellipsoid_distance(origin, direction, center, radii):
    ox = (origin[0] - center[0]) / max(0.001, radii[0])
    oy = (origin[1] - center[1]) / max(0.001, radii[1])
    oz = (origin[2] - center[2]) / max(0.001, radii[2])
    dx = direction[0] / max(0.001, radii[0])
    dy = direction[1] / max(0.001, radii[1])
    dz = direction[2] / max(0.001, radii[2])
    a = dx*dx + dy*dy + dz*dz
    b = 2.0 * (ox*dx + oy*dy + oz*dz)
    c = ox*ox + oy*oy + oz*oz - 1.0
    disc = b*b - 4.0*a*c
    if disc < 0.0 or a <= 1e-9:
        return None
    root = math.sqrt(disc)
    t1 = (-b - root) / (2.0*a)
    t2 = (-b + root) / (2.0*a)
    if t1 >= 0.05:
        return t1
    if t2 >= 0.05:
        return t2
    return None


def _ray_aabb_distance(origin, direction, bounds):
    t_min, t_max = 0.0, 100.0
    for axis in range(3):
        lo, hi = bounds[axis]
        o, d = origin[axis], direction[axis]
        if abs(d) < 1e-8:
            if o < lo or o > hi:
                return None
            continue
        t1 = (lo - o) / d
        t2 = (hi - o) / d
        if t1 > t2:
            t1, t2 = t2, t1
        t_min = max(t_min, t1)
        t_max = min(t_max, t2)
        if t_min > t_max:
            return None
    return t_min if t_min >= 0.05 else t_max if t_max >= 0.05 else None


def _end_ray_first_blocker(origin, direction, max_range=75.0):
    """End Stone floor, arena edge and obsidian towers stop bullets."""
    blocker = max_range
    hit_any = False


    if direction[1] < -1e-8:
        t_floor = (-2.25 - origin[1]) / direction[1]
        if 0.05 < t_floor < blocker:
            x = origin[0] + direction[0] * t_floor
            z = origin[2] + direction[2] * t_floor
            if -12.0 <= x <= 12.0 and 5.0 <= z <= 39.0:
                blocker, hit_any = t_floor, True


    edge_t = max_range
    if direction[0] > 1e-8:
        edge_t = min(edge_t, (12.0 - origin[0]) / direction[0])
    elif direction[0] < -1e-8:
        edge_t = min(edge_t, (-12.0 - origin[0]) / direction[0])
    if direction[2] > 1e-8:
        edge_t = min(edge_t, (39.0 - origin[2]) / direction[2])
    elif direction[2] < -1e-8:
        edge_t = min(edge_t, (5.0 - origin[2]) / direction[2])
    if 0.05 < edge_t < blocker:
        blocker, hit_any = edge_t, True


    for tx, tz in ((-8.5, 15.0), (8.5, 15.0), (-8.5, 32.0), (8.5, 32.0)):
        t_box = _ray_aabb_distance(
            origin, direction,
            ((tx - 0.96, tx + 0.96), (-2.25, 1.78), (tz - 0.96, tz + 0.96))
        )
        if t_box is not None and 0.05 < t_box < blocker:
            blocker, hit_any = t_box, True
    return blocker, hit_any


def _end_dragon_ray_hit(origin, direction, max_range=75.0):
    root_x, root_y, root_z, flap = get_end_dragon_pose()


    shapes = [
        ((root_x, root_y + 0.06, root_z + 0.20), (0.92, 0.54, 1.72)),
        ((root_x, root_y + 0.16, root_z - 2.30), (0.63, 0.43, 0.82)),
        ((root_x, root_y - 0.08, root_z + 3.35), (0.28, 0.24, 1.55)),
        ((root_x - 2.65, root_y + 0.78 + flap*0.22, root_z + 0.72), (2.55, 0.23, 1.48)),
        ((root_x + 2.65, root_y + 0.78 + flap*0.22, root_z + 0.72), (2.55, 0.23, 1.48)),
    ]
    best = None
    for center, radii in shapes:
        t_hit = _ray_ellipsoid_distance(origin, direction, center, radii)
        if t_hit is not None and t_hit < max_range and (best is None or t_hit < best):
            best = t_hit
    blocker, blocked = _end_ray_first_blocker(origin, direction, max_range)
    if best is not None and best < blocker - 0.04:
        return best, True
    return blocker, False


def fire_end_weapon():
    """Fires the equipped weapon along the real End camera ray."""
    global shoot_cooldown, recoil_offset, muzzle_light, minigun_spin
    global end_dragon_hp, end_dragon_hit_flash, screen_shake, game_state, end_crystal_hp
    if game_state != STATE_END or not has_gun or shoot_cooldown > 0 or market_open or _adm_open or paused or not _verify_gl_integrity() or not _adm_state_valid():
        return

    weapon = current_weapon if current_weapon in WEAPONS else "PISTOL"
    w_stats = _gl_wep_shader(weapon)


    shoot_cooldown = max(1, int(w_stats[1]))
    recoil_offset = max(recoil_offset, float(w_stats[5]))
    muzzle_light = 1.0
    if w_stats[3] or _adm_hyper:
        minigun_spin += 0.9

    yaw = end_cam_yaw
    pitch = end_cam_pitch
    direction = (math.sin(yaw) * math.cos(pitch), math.sin(pitch), math.cos(yaw) * math.cos(pitch))
    origin = (end_cam_x, -0.70, end_cam_z)
    hit_distance, hit_dragon = _end_dragon_ray_hit(origin, direction)

    crystal_hit = None
    crystal_positions = [(-8.5, 15.0), (8.5, 15.0), (-8.5, 32.0), (8.5, 32.0)]
    blocker_distance, _ = _end_ray_first_blocker(origin, direction)
    for ci, (cx, cz) in enumerate(crystal_positions):
        if end_crystal_hp[ci] <= 0:
            continue
        t_core = _ray_ellipsoid_distance(origin, direction, (cx, 2.35, cz), (0.48, 0.78, 0.48))
        if t_core is not None and t_core < blocker_distance and (crystal_hit is None or t_core < crystal_hit[0]):
            crystal_hit = (t_core, ci)
    if crystal_hit is not None and (not hit_dragon or crystal_hit[0] < hit_distance):
        hit_distance, hit_dragon = crystal_hit[0], False
        ci = crystal_hit[1]
        end_crystal_hp[ci] = max(0.0, end_crystal_hp[ci] - max(1.0, float(w_stats[2])))
        spawn_hit_particles(origin[0] + direction[0]*hit_distance, 2.35,
                            origin[2] + direction[2]*hit_distance, (190, 95, 255),
                            count=10, speed_mult=0.9, size_mult=1.2)
        if end_crystal_hp[ci] <= 0:

            cx, cz = crystal_positions[ci]
            spawn_hit_particles(cx, 2.35, cz, (235, 175, 255),
                                count=42, speed_mult=2.15, size_mult=2.25)
            spawn_hit_particles(cx, 2.35, cz, (115, 225, 255),
                                count=22, speed_mult=1.65, size_mult=1.65)
            spawn_hit_particles(cx, 2.35, cz, (255, 255, 225),
                                count=14, speed_mult=2.6, size_mult=1.25)
            screen_shake = max(screen_shake, 7.0)
            muzzle_light = max(muzzle_light, 0.9)
    impact = (origin[0] + direction[0] * hit_distance,
              origin[1] + direction[1] * hit_distance,
              origin[2] + direction[2] * hit_distance)

    if hit_dragon:

        damage = end_dragon_hp if _adm_oneshot else max(1.0, float(w_stats[2]))
        end_dragon_hp = max(0.0, end_dragon_hp - damage)
        end_dragon_hit_flash = 0.20
        screen_shake = max(screen_shake, 2.2)
        spawn_hit_particles(impact[0], impact[1], impact[2], (210, 95, 255), count=7, speed_mult=0.8, size_mult=1.3)
        if end_dragon_hp <= 0:
            end_dragon_hp = 0.0
            global end_credits_start
            game_state = STATE_WIN
            end_credits_start = pygame.time.get_ticks()
    else:

        spawn_hit_particles(impact[0], max(-2.0, impact[1]), impact[2], (205, 185, 125), count=3, speed_mult=0.45, size_mult=0.8)

    end_shots.append([origin, impact, 0.10, WEAPONS[weapon]["tracer_col"], 4 if weapon == "RPG" else 2])
    if len(end_shots) > 8:
        del end_shots[:-8]


def _update_end_fireballs(dt):
    """Aggressive but dodgeable dragon attacks with short predictive lead."""
    global end_attack_timer, _sys_vit_gauge, damage_flash, screen_shake, game_state, gameover_reason
    global end_dragon_hit_flash, end_dragon_hp, end_dragon_max_hp, end_crystal_hp
    end_attack_timer -= dt

    if any(hp > 0 for hp in end_crystal_hp) and end_dragon_hp > 0:
        global end_crystal_heal_timer
        end_crystal_heal_timer += dt
        if end_crystal_heal_timer >= 1.25:
            end_crystal_heal_timer -= 1.25
            end_dragon_hp = min(end_dragon_max_hp, end_dragon_hp + 8.0 * sum(1 for hp in end_crystal_hp if hp > 0))
    if end_attack_timer <= 0.0 and end_dragon_hp > 0:
        root_x, root_y, root_z, _ = get_end_dragon_pose()
        start = (root_x, root_y + 0.12, root_z - 2.75)


        lead_t = 0.15
        predicted_x = end_cam_x + end_player_vx * lead_t
        predicted_z = end_cam_z + end_player_vz * lead_t
        dodge_offset = math.sin(end_dragon_phase * 1.4) * 2.4

        targets = [(predicted_x + dodge_offset, -0.48, predicted_z + 0.4)]
        for target in targets:
            dx, dy, dz = target[0]-start[0], target[1]-start[1], target[2]-start[2]
            length = max(0.001, math.sqrt(dx*dx + dy*dy + dz*dz))
            speed = 5.4
            end_fireballs.append([start[0], start[1], start[2], dx/length*speed,
                                  dy/length*speed, dz/length*speed, 7.0])
        if len(end_fireballs) > 8:
            del end_fireballs[:-8]
        end_attack_timer = random.uniform(4.2, 5.2)

    for orb in end_fireballs[:]:
        orb[0] += orb[3] * dt
        orb[1] += orb[4] * dt
        orb[2] += orb[5] * dt
        orb[6] -= dt
        if math.dist((orb[0], orb[1], orb[2]), (end_cam_x, -0.70, end_cam_z)) < 0.92:
            if not _adm_god:
                _apply_armor_damage(18.0)
                damage_flash = 12
                screen_shake = max(screen_shake, 7.0)
            spawn_hit_particles(orb[0], orb[1], orb[2], (255, 105, 35), count=15, speed_mult=1.35, size_mult=1.7)
            end_fireballs.remove(orb)
            if _sys_vit_gauge <= 0 and not _adm_god:
                gameover_reason = "ENDER EJDERHASININ ATEŞ TOPUYLA VURULDUN!"
                game_state = STATE_GAMEOVER
                return
        elif orb[6] <= 0.0 or orb[1] < -2.0 or abs(orb[0]) > 13.0 or not (4.0 <= orb[2] <= 40.0):
            end_fireballs.remove(orb)

    for shot in end_shots[:]:
        shot[2] -= dt
        if shot[2] <= 0.0:
            end_shots.remove(shot)
    end_dragon_hit_flash = max(0.0, end_dragon_hit_flash - dt)


def process_menu_or_ui_tap(tx, ty):
    global ui_click_cooldown, net_mode, game_state, input_pin_text, input_host_ip, active_input_field
    global market_open, _adm_open
    global game_mode, _network_stop_event
    global end_cam_x, end_cam_z, end_cam_yaw, end_cam_pitch
    global end_attack_timer, end_dragon_hit_flash
    global has_gun, current_weapon, owned_weapons
    global end_player_vx, end_player_vz
    if ui_click_cooldown > 0:
        return
    ui_click_cooldown = 10

    if game_state == STATE_MENU:
        if singleplayer_btn_rect.collidepoint(tx, ty):

            _stop_network_session()
            reset_game()
            game_state = STATE_GAME
        elif multiplayer_btn_rect.collidepoint(tx, ty):
            game_state = STATE_MULTIPLAYER_MENU

    elif game_state == STATE_MULTIPLAYER_MENU:
        if host_btn_rect.collidepoint(tx, ty):
            game_state = STATE_HOST_PIN
        elif join_btn_rect.collidepoint(tx, ty):
            game_state = STATE_JOIN_PIN
        elif mp_back_btn_rect.collidepoint(tx, ty):
            game_state = STATE_MENU

    elif game_state == STATE_HOST_PIN:
        if pin_connect_btn.collidepoint(tx, ty):
            if len(input_pin_text) > 0:
                _stop_network_session()
                game_mode = "MULTI"
                net_mode = "HOST"
                port_num = pin_to_port(input_pin_text)
                threading.Thread(
                    target=network_server_thread,
                    args=(port_num, _network_stop_event),
                    daemon=True
                ).start()
                reset_game()
                game_state = STATE_GAME
            return True
        for rect, char in keyboard_buttons:
            if rect.collidepoint(tx, ty):
                if char == "SİL":
                    input_pin_text = input_pin_text[:-1]
                elif char.isdigit() and len(input_pin_text) < 6:
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
                _stop_network_session()
                game_mode = "MULTI"
                net_mode = "CLIENT"
                port_num = pin_to_port(input_pin_text)
                threading.Thread(
                    target=network_client_thread,
                    args=(input_host_ip, port_num, _network_stop_event),
                    daemon=True
                ).start()
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
                    if active_input_field == "PIN" and char.isdigit() and len(input_pin_text) < 6:
                        input_pin_text += char
                    elif active_input_field == "IP" and len(input_host_ip) < 18:
                        input_host_ip += char
                return True

    elif game_state == STATE_END:
        if market_open:
            handle_market_click(tx, ty)
            return True
        if _adm_open:
            handle_admin_click(tx, ty)
            return True
        if end_market_btn_rect.collidepoint(tx, ty):
            market_open = True
            active_touches.clear()
            touch_roles.clear()
            touch_last_pos.clear()
            return True
        if _adm_unlocked and end_admin_btn_rect.collidepoint(tx, ty):
            _adm_open = True
            active_touches.clear()
            touch_roles.clear()
            touch_last_pos.clear()
            return True
        if math.hypot(tx - shoot_btn_center[0], ty - shoot_btn_center[1]) <= shoot_btn_radius * 1.25:
            fire_weapon()
            return True
    elif game_state in (STATE_GAMEOVER, STATE_WIN):
        if play_btn_rect.collidepoint(tx, ty):
            reset_game()
            game_state = STATE_GAME
            return True

    elif game_state == STATE_GAME:
        if active_dimension == "OVERWORLD" and game_mode != "MULTI" and net_mode is None and end_portal_unlocked and end_portal_screen_rect.width > 0 and end_portal_screen_rect.inflate(34, 28).collidepoint(tx, ty):
            global end_dragon_hp, end_dragon_phase, end_crystal_hp, end_crystal_heal_timer
            end_dragon_hp = end_dragon_max_hp
            end_crystal_hp = [end_crystal_max_hp] * 4
            end_crystal_heal_timer = 0.0
            end_dragon_phase = 0.0
            end_fireballs.clear()
            end_shots.clear()
            end_attack_timer = 4.2
            end_dragon_hit_flash = 0.0

            if not has_gun:
                has_gun = True
                current_weapon = "PISTOL"
                owned_weapons.add("PISTOL")
            end_cam_x, end_cam_z = 0.0, 11.5
            end_cam_yaw, end_cam_pitch = 0.0, 0.0
            end_player_vx = end_player_vz = 0.0
            end_fireballs.clear()
            end_shots.clear()
            try:

                game_state = STATE_END
            except Exception as end_enter_error:
                print("END GİRİŞ HATASI:", repr(end_enter_error))
                game_state = STATE_GAME
            return True
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







import os as _eco_os
import zlib as _eco_zlib
import marshal as _eco_marshal
import types as _eco_types
import struct as _eco_struct

_ECO_TABLE = 'c-mExUu(iJ6ve+wo<q1zlh*py%^=14hw2ziM2hQ}pjN7~2l2b_+_X~{NSaH3Ip^M+Tt(UJ>t=mywwvlC`b(05CaEn+LnI@76QY&uu%`OFY|h*Iz@#EcD!|k{EtZfMV}WnVqv$8?KvbX3EDky7Lz84kUbZ?^`z;$^#cSc*%oV__m0B6O)GEX#SxFOlFXW_He3s>TI`n7{O3JoqsGw+chZ09(K61HROea7MtW{4gc>%scp}=}~^gS&GjzNvoxC8hD-Kb3=;ZQ&5kLma&b4+ux#IgxCNKeyK1~)0bt8yp$UQYZ}<*`2aa?`;$o2-X#>=^jI_@d9vrQ(x;iMgwB@^8eQdpa_)FNvf@RgYtu?;^4t28Zm)K?Buy)abt(Bj3~cVw$%PAOuJ9tK6MDNY=+KSImZh@Frv!wH>^3zP%9_eftFlUXSP'
_ECO_DEFINITION_DIGEST = 'df25edd9c3b7420a7c62e02553068e7b05a5cee960e8c27846ff34072ed4dbc2'
_EXPECTED_TABLE_DIGEST = "a90b0bf96930d49fa66f1b358e495ce549402ad31785681af4c7f90bdb13b248"
_ECO_READY = False
_ECONOMY_SEALS = ()
_ECO_WALLET_ID = None
_economy_warning = ''
_eco_previous_wep = _gl_wep_shader
_eco_previous_lod = _shd_lod_matrix


def _eco_bad(reason='Ekonomi doğrulaması başarısız'):
    global _gl_render_lock_state, _economy_warning
    _gl_render_lock_state = True
    _economy_warning = reason + '. Satın alma ve ödüller durduruldu; oyunu yeniden başlatın.'
    return False


def _eco_unpack():
    raw = _eco_zlib.decompress(base64.b85decode(_ECO_TABLE.encode('ascii')))
    if not hmac.compare_digest(hashlib.sha256(raw).hexdigest(), _ECO_DEFINITION_DIGEST):
        raise ValueError('Canonical economy definition changed')
    return json.loads(raw.decode('utf-8'))


try:
    _eco_defs = _eco_unpack()
except Exception:


    _eco_bad('Ekonomi tablosu okunamadı')
    _eco_defs = {
        'weapons': {k: list(_eco_previous_wep(k)) for k in WEAPONS},
        'enemies': {k: list(_eco_previous_lod(k)) for k in ENEMY_TYPES},
        'armor_prices': list(armor_prices), 'armor_reduction': list(armor_reduction),
        'costs': [_k_adm_cost, _k_med_cost, _k_start_bal, _k_adm_gun_cost],
        'cap': 9999999, 'heal': 50.0,
    }


_k_adm_cost, _k_med_cost, _k_start_bal, _k_adm_gun_cost = _eco_defs['costs']
armor_prices = list(_eco_defs['armor_prices'])
armor_reduction = list(_eco_defs['armor_reduction'])
_ENEMY_ORDER_FOR_DIGEST = tuple(sorted(_eco_defs['enemies']))


def _eco_tuple(value):
    return tuple(_eco_tuple(v) for v in value) if isinstance(value, (list, tuple)) else value


def _gl_wep_shader(_w_id):
    return _eco_tuple(_eco_defs['weapons'][_w_id])


def _shd_lod_matrix(_tag):
    return _eco_tuple(_eco_defs['enemies'][_tag])


def _eco_amount(value):


    return type(value) is int and 0 <= value <= _eco_defs['cap']


def _eco_code_data(code):
    consts = tuple(_eco_code_data(c) if isinstance(c, _eco_types.CodeType) else c
                   for c in code.co_consts)
    return (code.co_code, consts, code.co_names, code.co_varnames,
            code.co_freevars, code.co_cellvars, code.co_argcount,
            getattr(code, 'co_posonlyargcount', 0), code.co_kwonlyargcount,
            code.co_nlocals, code.co_stacksize, code.co_flags,
            getattr(code, 'co_exceptiontable', b''))


def _code_seal(func):
    code = getattr(func, '__code__', None)
    if code is None:
        return ''


    payload = (_eco_code_data(code), getattr(func, '__defaults__', None),
               getattr(func, '__kwdefaults__', None))
    return hashlib.sha256(_eco_marshal.dumps(payload, 2)).hexdigest()


def _current_table_digest():
    snapshot = {
        'blob': _ECO_TABLE, 'definition_digest': _ECO_DEFINITION_DIGEST,
        'canonical': _eco_defs,
        'weapons': [(k, _gl_wep_shader(k)) for k in sorted(_eco_defs['weapons'])],
        'enemies': [(k, _shd_lod_matrix(k)) for k in _ENEMY_ORDER_FOR_DIGEST],
        'enemy_keys': sorted(ENEMY_TYPES), 'weapon_order': list(WEAPON_ORDER),
        'armor_prices': list(armor_prices), 'armor_reduction': list(armor_reduction),
        'costs': [_k_adm_cost, _k_med_cost, _k_start_bal, _k_adm_gun_cost],
    }
    raw = json.dumps(snapshot, sort_keys=True, separators=(',', ':'), allow_nan=False)
    return hashlib.sha256(raw.encode('utf-8')).hexdigest()


def _eco_resolve(name):
    if name.startswith('wallet.'):
        return getattr(_RtSyncState, name.split('.', 1)[1], None)
    return globals().get(name)


def _init_economy_seals():
    """Call ONCE after all parent/Nether wrappers, before reset_game/loop.

    The parent must regenerate _EXPECTED_TABLE_DIGEST as a literal in the
    delivered source. Never assign that expected digest dynamically at runtime.
    """
    global _ECO_READY, _ECONOMY_SEALS, _WALLET_STORE_SEAL, _ECO_WALLET_ID
    if _ECO_READY:
        return _verify_gl_integrity()
    names = [n for n, obj in globals().items() if callable(obj) and
             (n.startswith('_eco_') or n in (
                 '_gl_wep_shader', '_shd_lod_matrix', '_reward_for',
                 '_register_enemy', '_code_seal', '_current_table_digest',
                 '_verify_gl_integrity', '_init_economy_seals', '_purchase_item',
                 '_adm_state_valid', '_sys_shader_cache_probe', 'handle_market_click',
                 'on_enemy_killed', 'spawn_enemy', 'reset_game', 'fire_weapon',
                 'fire_end_weapon', '_server_apply_remote_shot'))
             and getattr(obj, '__code__', None) is not None]
    names += ['wallet.' + n for n, obj in vars(_RtSyncState).items()
              if callable(obj) and getattr(obj, '__code__', None) is not None]
    _ECONOMY_SEALS = tuple((n, _eco_resolve(n), _code_seal(_eco_resolve(n)))
                          for n in sorted(names))
    _ECO_WALLET_ID = id(_rt_wallet)
    _WALLET_STORE_SEAL = _code_seal(_RtSyncState._store)
    _ECO_READY = True
    return _verify_gl_integrity()


def _verify_gl_integrity():
    if _gl_render_lock_state or not _ECO_READY:
        return False
    try:
        if type(_rt_wallet) is not _RtSyncState or id(_rt_wallet) != _ECO_WALLET_ID:
            return _eco_bad('Cüzdan nesnesi değiştirildi')
        for name, original, expected in _ECONOMY_SEALS:
            current = _eco_resolve(name)
            if current is not original or _code_seal(current) != expected:
                return _eco_bad('Ekonomi işlevi değiştirildi')
        if set(_ENEMY_ORDER_FOR_DIGEST) != set(ENEMY_TYPES):
            return _eco_bad('Düşman ödül tablosu eksik')
        if not hmac.compare_digest(_current_table_digest(), _EXPECTED_TABLE_DIGEST):
            return _eco_bad('Fiyat veya istatistik tablosu değiştirildi')
    except Exception:
        return _eco_bad()
    return True


def _reward_for(en):
    """Canonical reward only; NEVER trust mutable en['_b_val']."""
    if not isinstance(en, dict) or not _verify_gl_integrity():
        return None
    tag = en.get('type')
    if tag not in _ENEMY_ORDER_FOR_DIGEST:
        return None

    row = _eco_defs['enemies'].get(tag)
    reward = row[0] if row is not None else _shd_lod_matrix(tag)[0]
    return reward if _eco_amount(reward) else None


class _RtSyncState:
    """Ephemeral masked wallet with independent shadows and per-process HMAC.

    A copied entire state/key or modified source can still defeat this; it is
    corruption detection and cheat resistance, not a trusted financial ledger.
    Legacy add(delta) remains callable but raw self-crediting is disabled.
    """
    __slots__ = ('_lock', '_key', '_permit', '_m', '_e', '_m2', '_l', '_n', '_p',
                 '_version', '_tag', '_pending', '_counter')

    def __init__(self):
        self._lock = threading.RLock()
        self._key = _eco_os.urandom(32)
        self._permit = object()
        self._version = self._counter = 0
        self._pending = {}
        self._store(0, self._permit)

    def _mac(self):
        raw = _eco_struct.pack('>7Q', self._m, self._e, self._m2, self._l,
                               self._n, self._p, self._version)
        return hmac.new(self._key, raw, hashlib.sha256).digest()

    def _store(self, value, permit=None):
        if permit is not self._permit or not _eco_amount(value):
            return False
        self._m, self._m2, self._n = (int.from_bytes(_eco_os.urandom(8), 'big')
                                      for _ in range(3))
        self._e = value ^ self._m
        self._l = (value * 3 + 0x5F3) ^ self._m2
        self._p = (value + 0x6D2B79F5) ^ self._n
        self._version += 1
        self._tag = self._mac()
        return True

    def _peek(self):
        try:
            if not hmac.compare_digest(self._mac(), self._tag):
                return None
            value = self._e ^ self._m
            if not _eco_amount(value):
                return None
            if self._l != ((value * 3 + 0x5F3) ^ self._m2):
                return None
            if self._p != ((value + 0x6D2B79F5) ^ self._n):
                return None
            return value
        except Exception:
            return None

    def get(self):
        with self._lock:
            value = self._peek()
            if value is None:
                _eco_bad('Cüzdan doğrulaması başarısız')
                self._store(0, self._permit)
                return 0
            return value

    def reset(self):
        with self._lock:
            start = _eco_defs['costs'][2]
            if not _eco_amount(start) or _k_start_bal != start or not _verify_gl_integrity():
                return False
            self._pending.clear()
            return self._store(start, self._permit)

    def zero(self):
        with self._lock:
            return self._store(0, self._permit)

    def add(self, delta):


        if not _eco_amount(delta):
            return False
        return False

    def try_spend(self, amount):
        with self._lock:
            if net_mode == 'CLIENT' or not _eco_amount(amount) or not _verify_gl_integrity():
                return False
            value = self._peek()
            if value is None:
                self.get()
                return False
            return self._store(value - amount, self._permit) if value >= amount else False

    def host_sync(self, value):
        if net_mode != 'CLIENT' or not _eco_amount(value) or not _verify_gl_integrity():
            return False
        with self._lock:
            return self._store(value, self._permit)

    def _register(self, en):
        with self._lock:
            if not isinstance(en, dict) or en.get('type') not in _ENEMY_ORDER_FOR_DIGEST:
                return False
            if not any(candidate is en for candidate in enemies):
                return False
            key = id(en)
            if key in self._pending:
                return self._pending[key][0] is en
            if '_eco_ticket' in en:
                return False
            self._counter += 1
            tag = en['type']
            raw = ('%s|%s|%s' % (key, self._counter, tag)).encode('utf-8')
            ticket = hmac.new(self._key, raw, hashlib.sha256).hexdigest()
            self._pending[key] = (en, tag, ticket)
            en['_eco_ticket'] = ticket
            return True

    def award(self, en):
        with self._lock:
            if net_mode == 'CLIENT' or not isinstance(en, dict):
                return False
            record = self._pending.get(id(en))
            if record is None or record[0] is not en:
                return False
            if en.get('type') != record[1] or en.get('_eco_ticket') != record[2]:
                return _eco_bad('Düşman ödül kaydı değiştirildi')
            reward = _reward_for(en)
            value = self._peek()
            if reward is None or value is None:
                if value is None:
                    self.get()
                return False
            if not self._store(min(_eco_defs['cap'], value + reward), self._permit):
                return False
            del self._pending[id(en)]
            return True


_rt_wallet = _RtSyncState()
_WALLET_STORE_SEAL = _code_seal(_RtSyncState._store)


def _register_enemy(en):
    """Call for every freshly appended enemy (also Nether custom spawns)."""
    with _rt_wallet._lock:
        live = {id(candidate) for candidate in enemies}
        for key in tuple(_rt_wallet._pending):
            if key not in live:
                del _rt_wallet._pending[key]
        return _rt_wallet._register(en)


_eco_previous_spawn = spawn_enemy


def spawn_enemy(*args, **kwargs):
    result = _eco_previous_spawn(*args, **kwargs)


    with _rt_wallet._lock:
        live = {id(en) for en in enemies}
        for key in tuple(_rt_wallet._pending):
            if key not in live:
                del _rt_wallet._pending[key]
        for en in enemies:
            _register_enemy(en)
    return result


def _adm_state_valid():
    global _adm_unlocked, _adm_open, _adm_oneshot, _adm_god, _adm_freeze, _adm_hyper
    expected = hashlib.sha256(f'{_adm_proof_salt}|adm_valid_{_k_adm_cost}'.encode('utf-8')).hexdigest()
    invalid = (_adm_unlocked and not hmac.compare_digest(str(_adm_proof), expected))
    invalid = invalid or (not _adm_unlocked and any((_adm_oneshot, _adm_god, _adm_freeze, _adm_hyper)))
    if invalid:
        _adm_unlocked = _adm_open = _adm_oneshot = _adm_god = _adm_freeze = _adm_hyper = False
        return _eco_bad('Admin satın alma kanıtı geçersiz')
    return True


def _purchase_item(stock_code):
    """Atomic authoritative purchase/equip. Return True only on success.

    Codes: weapon:AK47, weapon:ADMIN_GUN, armor:1..5, heal, admin.
    CLIENT purchasing is denied until authoritative inventory sync exists.
    """
    global current_weapon, armor_level, _sys_vit_gauge, _adm_unlocked
    global _adm_proof, _adm_open, market_open
    with _rt_wallet._lock:
        if net_mode == 'CLIENT' or type(stock_code) is not str:
            return False
        if not _verify_gl_integrity() or not _adm_state_valid():
            return False
        if not isinstance(owned_weapons, set) or not owned_weapons <= set(_eco_defs['weapons']):
            return _eco_bad('Silah sahipliği geçersiz')
        if type(armor_level) is not int or not 0 <= armor_level < len(armor_prices):
            return _eco_bad('Zırh sahipliği geçersiz')
        action, value = None, None
        if stock_code.startswith('weapon:'):
            value = stock_code.split(':', 1)[1]
            if value not in _eco_defs['weapons']:
                return False
            if value in owned_weapons:
                current_weapon = value
                return True
            price = _eco_defs['costs'][3] if value == 'ADMIN_GUN' else _eco_defs['weapons'][value][0]
            action = 'weapon'
        elif stock_code in tuple('armor:' + str(i) for i in range(1, len(armor_prices))):
            value = int(stock_code.split(':', 1)[1])
            if value <= armor_level:
                return False
            price, action = _eco_defs['armor_prices'][value], 'armor'
        elif stock_code == 'heal':
            if type(_sys_vit_gauge) not in (int, float) or not math.isfinite(_sys_vit_gauge):
                return False
            if not 0 < _sys_vit_gauge < 100.0:
                return False
            price, action = _eco_defs['costs'][1], 'heal'
        elif stock_code == 'admin':
            if _adm_unlocked:
                market_open, _adm_open = False, True
                return True
            price, action = _eco_defs['costs'][0], 'admin'
        else:
            return False
        if not _rt_wallet.try_spend(price):
            return False
        if action == 'weapon':
            owned_weapons.add(value)
            current_weapon = value
        elif action == 'armor':
            armor_level = value
        elif action == 'heal':
            _sys_vit_gauge = min(100.0, _sys_vit_gauge + _eco_defs['heal'])
        elif action == 'admin':
            _adm_proof = hashlib.sha256(f'{_adm_proof_salt}|adm_valid_{price}'.encode('utf-8')).hexdigest()
            _adm_unlocked, market_open, _adm_open = True, False, True
        return True


def handle_market_click(tx, ty):
    global market_open, market_tab
    if market_close_rect.collidepoint(tx, ty):
        market_open = False
        return True
    if market_weapons_tab_rect.collidepoint(tx, ty):
        market_tab = 'weapons'
        return True
    if market_armor_tab_rect.collidepoint(tx, ty):
        market_tab = 'armor'
        return True
    for idx, rect in enumerate(market_item_rects):
        if rect.collidepoint(tx, ty):
            if market_tab == 'armor':
                code = 'armor:' + str(idx + 1)
            elif idx < len(WEAPON_ORDER):
                code = 'weapon:' + WEAPON_ORDER[idx]
            else:
                code = {4: 'weapon:ADMIN_GUN', 5: 'heal', 6: 'admin'}.get(idx, '')
            _purchase_item(code)
            return True
    return False

















































STATE_NETHER = 'NETHER'
active_dimension = 'OVERWORLD'
NETHER_ENEMY_ORDER = (
    'PIGLIN', 'ZOMBIFIED_PIGLIN', 'HOGLIN', 'ZOGLIN', 'BLAZE', 'GHAST',
    'MAGMA_CUBE', 'WITHER_SKELETON', 'ENDERMAN', 'STRIDER', 'WITHER'
)
_nether_names = {
    'PIGLIN': 'Piglin', 'ZOMBIFIED_PIGLIN': 'Zombi Piglin', 'HOGLIN': 'Hoglin',
    'ZOGLIN': 'Zoglin', 'BLAZE': 'Blaze', 'GHAST': 'Ghast',
    'MAGMA_CUBE': 'Magma Küpü', 'WITHER_SKELETON': 'Wither İskeleti',
    'ENDERMAN': 'Enderman', 'STRIDER': 'Strider', 'WITHER': 'WITHER'
}
ENEMY_TYPES.update({t: {'name': n} for t, n in _nether_names.items()})
_nether_base_lod = _shd_lod_matrix
_nether_base_spawn = spawn_enemy
_nether_base_killed = on_enemy_killed
_nether_base_warden = check_warden_boss_trigger
_nether_base_polygons = get_enemy_polygons


def _shd_lod_matrix(_tag):

    if _tag not in NETHER_ENEMY_ORDER:
        return _nether_base_lod(_tag)
    cfg = {
        'PIGLIN': ('PILLAGER', 7.0, (2.0, 2.6), 13.0, 7.0, 0.0),
        'ZOMBIFIED_PIGLIN': ('ZOMBIE', 8.0, (1.7, 2.3), 15.0, 0.0, 0.0),
        'HOGLIN': ('PILLAGER', 14.0, (2.1, 2.8), 18.0, 0.0, 0.0),
        'ZOGLIN': ('PILLAGER', 16.0, (2.3, 2.9), 20.0, 0.0, 0.0),
        'BLAZE': ('SKELETON', 9.0, (1.3, 1.8), 8.0, 10.0, 0.0),
        'GHAST': ('PILLAGER', 18.0, (0.8, 1.2), 0.0, 16.0, 2.5),
        'MAGMA_CUBE': ('CREEPER', 10.0, (1.8, 2.4), 14.0, 0.0, 0.0),
        'WITHER_SKELETON': ('PILLAGER', 12.0, (2.0, 2.6), 17.0, 0.0, 0.0),
        'ENDERMAN': ('PILLAGER', 15.0, (3.1, 3.8), 19.0, 0.0, 0.0),
        'STRIDER': ('ZOMBIE', 5.0, (1.1, 1.5), 0.0, 0.0, 0.0),
        'WITHER': ('WARDEN', 180.0, (1.5, 2.0), 15.0, 22.0, 3.0)
    }[_tag]


    stats = tuple(tuple(float(str(v)) for v in item) if isinstance(item,tuple)
                  else float(str(item)) for item in cfg[1:])
    return (_nether_base_lod(cfg[0])[0],) + stats


NETHER_RESOURCE_NAMES = {
    'gold_nuggets': 'Altın Parçası', 'quartz': 'Kuvars',
    'glowstone_dust': 'Işıktaşı Tozu', 'ancient_debris': 'Antik Kalıntı',
    'blaze_rods': 'Blaze Çubuğu', 'wither_skulls': 'Wither Kafası',
    'ender_pearls': 'Ender İncisi', 'soul_sand': 'Ruh Kumu',
    'crimson_mushrooms': 'Kızıl Mantar', 'warped_mushrooms': 'Çarpık Mantar',
    'blackstone': 'Karataş', 'basalt': 'Bazalt', 'magma_cream': 'Magma Kremi',
    'leather': 'Deri', 'string': 'İp', 'netherite_ingots': 'Netherit Külçesi',
    'nether_star': 'Nether Yıldızı', 'obsidian': 'Obsidyen'
}
nether_inventory = {k: 0 for k in NETHER_RESOURCE_NAMES}
nether_inventory_open = False
nether_kills = 0
nether_wither_defeated = False
nether_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
nether_inventory_rect = pygame.Rect(int(WIDTH*.03), int(HEIGHT*.132),
                                   int(WIDTH*.29), int(HEIGHT*.052))
nether_action_rect = pygame.Rect(int(WIDTH*.40), VIEW_H + 8,
                               int(WIDTH*.56), int(HEIGHT*.060))
_nether_panel = pygame.Rect(int(WIDTH*.03), int(HEIGHT*.19),
                           int(WIDTH*.94), int(HEIGHT*.50))
_nether_recipe_rects = [pygame.Rect(int(WIDTH*.06), int(HEIGHT*(.51+i*.040)),
                                  int(WIDTH*.88), int(HEIGHT*.034))
                        for i in range(4)]
_nether_close_rect = pygame.Rect(int(WIDTH*.35), int(HEIGHT*.665),
                                int(WIDTH*.30), int(HEIGHT*.038))
_nether_overworld = None
_nether_saved = None
_nether_nodes = []
_nether_chests = []
_nether_lava = []
_nether_bridges = []
_nether_message = ''
_nether_message_until = 0
_nether_spawn_clock = 0.0
_nether_time = 0.0
_nether_mounted = None
_nether_prev_player = (0.0, 0.0)
_nether_burn_clock = 0.0
_nether_wither_clock = 0.0
_nether_boss_summoned = False
_nether_anchor_charges = 0
_nether_lodestone_bound = False
_nether_soul_speed = False
_nether_touch_cooldown = 0
NETHER_OVERWORLD_PORTAL = (-2.1, 3.1)
NETHER_RETURN_PORTAL = (0.0, -16.5)
NETHER_ALTAR = (0.0, 34.5)
NETHER_ANCHOR = (4.4, -10.5)
NETHER_LODESTONE = (2.7, 10.0)
NETHER_BIOMES = (
    ('WASTES', 'Nether Çoraklığı', (-23.5, 23.5, -20.5, -1.0), (107, 39, 35)),
    ('CRIMSON', 'Kızıl Orman', (-23.5, 0.0, -1.0, 19.0), (113, 28, 46)),
    ('WARPED', 'Çarpık Orman', (0.0, 23.5, -1.0, 19.0), (24, 97, 90)),
    ('SOUL', 'Ruh Kumu Vadisi', (-23.5, 0.0, 19.0, 41.0), (74, 63, 56)),
    ('BASALT', 'Bazalt Deltası', (0.0, 23.5, 19.0, 41.0), (58, 57, 66))
)


def _n_message(text, seconds=3.5):
    global _nether_message, _nether_message_until
    _nether_message = text
    _nether_message_until = pygame.time.get_ticks() + int(seconds*1000)


def nether_portal_unlocked():
    return has_gun and score >= 10


def _n_clear_transients():

    tracers.clear()
    particles.clear()
    enemy_arrows.clear()
    active_touches.clear()
    touch_roles.clear()
    touch_last_pos.clear()
    globals()['old_man_screen_rect'] = pygame.Rect(0, 0, 0, 0)
    globals()['end_portal_screen_rect'] = pygame.Rect(0, 0, 0, 0)


def _n_snapshot():
    return {
        'polygons': world_polygons[:], 'colliders': world_colliders[:],
        'lights': street_lights[:], 'enemies': enemies[:],


        'economy_pending': dict(_rt_wallet._pending) if hasattr(_rt_wallet,'_pending') else None,
        'camera': (cam_x, cam_y, cam_z, cam_yaw, cam_pitch),
        'palette': (SKY_TOP_COLOR, FOG_COLOR, GRASS_BG_COLOR),
        'dede': (troll_state, troll_timer, troll_pos[:], troll_anim, _dede_eliminated),
        'spawn_timer': spawn_timer, 'warden_active': warden_active,
        'dialog': (dialog_active, dialog_text, dialog_speaker, dialog_timer)
    }


def _n_restore(saved):
    global cam_x, cam_y, cam_z, cam_yaw, cam_pitch, spawn_timer
    global SKY_TOP_COLOR, FOG_COLOR, GRASS_BG_COLOR, warden_active
    global troll_state, troll_timer, troll_pos, troll_anim, _dede_eliminated
    global dialog_active, dialog_text, dialog_speaker, dialog_timer
    world_polygons[:] = saved['polygons']
    world_colliders[:] = saved['colliders']
    street_lights[:] = saved['lights']
    enemies[:] = saved['enemies']
    if saved.get('economy_pending') is not None and hasattr(_rt_wallet,'_pending'):
        with _rt_wallet._lock:
            _rt_wallet._pending.clear()
            _rt_wallet._pending.update(saved['economy_pending'])
    cam_x, cam_y, cam_z, cam_yaw, cam_pitch = saved['camera']
    SKY_TOP_COLOR, FOG_COLOR, GRASS_BG_COLOR = saved['palette']
    troll_state, troll_timer, troll_pos, troll_anim, _dede_eliminated = saved['dede']
    spawn_timer = saved['spawn_timer']
    warden_active = saved['warden_active']
    dialog_active, dialog_text, dialog_speaker, dialog_timer = saved['dialog']
    update_camera_trig()


def reset_nether():
    """Özgün reset_game EN BAŞINDA çağır: yeni oyun kaynakları sıfırlar."""
    global active_dimension, _nether_overworld, _nether_saved
    global nether_inventory_open, nether_kills, nether_wither_defeated
    global _nether_mounted, _nether_spawn_clock, _nether_time, _nether_boss_summoned
    global _nether_burn_clock, _nether_wither_clock, _nether_message_until
    global nether_portal_screen_rect, _nether_touch_cooldown
    global _nether_anchor_charges, _nether_lodestone_bound, _nether_soul_speed
    if active_dimension == 'NETHER' and _nether_overworld is not None:
        _n_restore(_nether_overworld)
    active_dimension = 'OVERWORLD'
    _nether_overworld = _nether_saved = None
    _nether_nodes.clear()
    _nether_chests.clear()
    _nether_lava.clear()
    _nether_bridges.clear()
    nether_inventory.clear()
    nether_inventory.update({k: 0 for k in NETHER_RESOURCE_NAMES})
    nether_inventory_open = False
    nether_kills = 0
    nether_wither_defeated = False
    _nether_mounted = None
    _nether_spawn_clock = _nether_time = 0.0
    _nether_burn_clock = _nether_wither_clock = 0.0
    _nether_boss_summoned = False
    _nether_anchor_charges = 0
    _nether_lodestone_bound = _nether_soul_speed = False
    _nether_message_until = _nether_touch_cooldown = 0
    nether_portal_screen_rect = pygame.Rect(0, 0, 0, 0)


def enter_nether():
    global active_dimension, _nether_overworld, _nether_prev_player
    global cam_x, cam_y, cam_z, cam_yaw, cam_pitch, warden_active
    global troll_state, _dede_eliminated, dialog_active, market_open, _adm_open
    global game_state, nether_inventory_open, _nether_mounted
    if game_mode == 'MULTI' or net_mode is not None:
        _n_message('Nether yalnız tek oyunculu: boyut ağ eşlemesi yok.', 5)
        return False
    if active_dimension == 'NETHER':
        return True
    if game_state != STATE_GAME or not nether_portal_unlocked():
        _n_message('Portal için silah ve köyde 10 leş gerekir.', 4)
        return False

    _nether_overworld = _n_snapshot()
    _n_clear_transients()
    active_dimension = 'NETHER'
    if _nether_saved is None:
        build_nether_world()
    else:
        _n_restore(_nether_saved)

    cam_x, cam_y, cam_z, cam_yaw, cam_pitch = 0.0, 1.75, -12.8, 0.0, 0.0
    troll_state = 'NORMAL'
    _dede_eliminated = True
    warden_active = False
    dialog_active = market_open = _adm_open = nether_inventory_open = False
    _nether_mounted = None
    _nether_prev_player = (cam_x, cam_z)
    game_state = STATE_GAME
    update_camera_trig()
    _n_message('Netherit: 4 altın damarlı kalıntı + 36 altın; ÇANTA > Külçe ÜRET.', 6)
    return True


def leave_nether():
    global active_dimension, _nether_saved, nether_inventory_open
    global _nether_mounted, _nether_wither_clock, _nether_burn_clock
    global game_state, nether_portal_screen_rect
    if active_dimension != 'NETHER' or _nether_overworld is None:
        return False
    _nether_saved = _n_snapshot()
    _n_restore(_nether_overworld)
    active_dimension = 'OVERWORLD'
    _nether_mounted = None
    _nether_wither_clock = _nether_burn_clock = 0.0
    nether_inventory_open = False
    game_state = STATE_GAME
    nether_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
    _n_clear_transients()
    _n_message('Köye döndün. Kaynakların ve Nether ilerlemen korunuyor.', 4)
    return True


def _n_poly(verts, color, unlit=True, bias=-.07):
    center, normal = compute_normal_and_center(verts)
    radius = max(math.dist(v, center) for v in verts)
    return (verts, color, unlit, center, bias, radius)


def _n_box(x, y, z, w, h, d, color, top=None):
    x1, x2, z1, z2, y2 = x-w/2, x+w/2, z-d/2, z+d/2, y+h
    return [
        _n_poly([(x1,y,z1),(x2,y,z1),(x2,y2,z1),(x1,y2,z1)],color),
        _n_poly([(x2,y,z2),(x1,y,z2),(x1,y2,z2),(x2,y2,z2)],color),
        _n_poly([(x1,y,z2),(x1,y,z1),(x1,y2,z1),(x1,y2,z2)],color),
        _n_poly([(x2,y,z1),(x2,y,z2),(x2,y2,z2),(x2,y2,z1)],color),
        _n_poly([(x1,y2,z1),(x2,y2,z1),(x2,y2,z2),(x1,y2,z2)],top or color)
    ]


def _n_floor(rect, color, y=.015):
    x1, x2, z1, z2 = rect
    add_quad((x1,y,z1),(x2,y,z1),(x2,y,z2),(x1,y,z2),color,
             unlit=True, layer_bias=.06)


def _n_rect_subtract(rect,masks):


    pieces=[rect]
    for a,b,c,d in masks:
        result=[]
        for x1,x2,z1,z2 in pieces:
            ix1,ix2,iz1,iz2=max(x1,a),min(x2,b),max(z1,c),min(z2,d)
            if ix1>=ix2 or iz1>=iz2:
                result.append((x1,x2,z1,z2))
                continue
            for part in [(x1,ix1,z1,z2),(ix2,x2,z1,z2),
                         (ix1,ix2,z1,iz1),(ix1,ix2,iz2,z2)]:
                if part[1]-part[0]>.01 and part[3]-part[2]>.01:
                    result.append(part)
        pieces=result
    return pieces


def _n_in_rect(x, z, rect, margin=0.0):
    a,b,c,d = rect
    return a-margin <= x <= b+margin and c-margin <= z <= d+margin


def nether_is_lava(x, z):
    if any(_n_in_rect(x,z,r,.12) for r in _nether_bridges):
        return False
    return any(_n_in_rect(x,z,r) for r in _nether_lava)


def nether_biome_at(x=None, z=None):
    x = cam_x if x is None else x
    z = cam_z if z is None else z
    for tag, name, rect, color in NETHER_BIOMES:
        if _n_in_rect(x,z,rect):
            return tag, name, color
    return 'WASTES', 'Nether Çoraklığı', (107,39,35)


def _n_solid(x, z, w, h, d, col):
    add_box(x,0,z,w,h,d,col,unlit=True)
    add_collider(x,z,w,d,max_y=h)


def _n_node(key, x, z, quantity, color):
    node = {'key':key,'x':x,'z':z,'quantity':quantity,'mined':False}
    if key=='ancient_debris':
        node['polygons'] = _n_box(x,.02,z,.78,.70,.78,(56,38,34),(114,73,52))
        node['polygons'] += _n_box(x-.12,.32,z-.402,.20,.19,.03,(220,142,59))
        node['polygons'] += _n_box(x+.16,.17,z-.402,.14,.12,.03,(246,199,97))
        node['polygons'] += _n_box(x,.59,z-.08,.34,.07,.13,(238,181,72))
    else:
        node['polygons'] = _n_box(x,.02,z,.68,.62,.68,(88,43,39),color)
        node['polygons'] += _n_box(x,.22,z-.347,.30,.17,.015,color)
    _nether_nodes.append(node)


def _n_chest(x,z,loot):
    _nether_chests.append({'x':x,'z':z,'loot':loot,'opened':False,
        'polygons':_n_box(x,.02,z,.90,.65,.65,(138,80,27),(192,126,44)) +
        _n_box(x,.29,z-.34,.12,.19,.025,(242,204,77))})


def _nether_lava_landings():
    return [(-19,-11,-6,-1)]


def build_nether_world():
    """Beş yerel biyom, köprüler, açık kale koridoru ve basamaklı bastion."""
    global SKY_TOP_COLOR, FOG_COLOR, GRASS_BG_COLOR
    world_polygons.clear()
    world_colliders.clear()
    street_lights.clear()
    enemies.clear()
    _nether_nodes.clear()
    _nether_chests.clear()
    _nether_lava[:] = [(-21,-6,-18,-9), (6,21,-18,-9),
                       (-21,-8,11,17), (7,21,22,29), (9,20,33,38)]
    _nether_bridges[:] = [(-2.7,2.7,-20,40),(-23,-2.7,6,9),(2.7,23,6,9),
                          (-23,-2.7,27,30),(2.7,23,27,30),
                          (-20,-7,-14.7,-12.9),(7,22,24.5,26.3),(5,9,-14.8,-12.8)]
    SKY_TOP_COLOR, FOG_COLOR, GRASS_BG_COLOR = (54,12,18),(91,30,29),(101,37,33)

    for tag, name, rect, col in NETHER_BIOMES:
        x1,x2,z1,z2 = rect
        x=x1
        while x < x2:
            z=z1
            while z < z2:
                tint = 5 if int(x+z)%2 else -5
                tile=(x,min(x+6,x2),z,min(z+6,z2))
                for part in _n_rect_subtract(tile,_nether_lava+_nether_bridges+_nether_lava_landings()):
                    _n_floor(part,tuple(max(0,c+tint) for c in col),.005)
                z += 6
            x += 6
    for pool in _nether_lava:
        for part in _n_rect_subtract(pool,_nether_bridges):
            _n_floor(part,(248,92,16),.030)
        a,b,c,d=pool
        for part in _n_rect_subtract((a+.3,b-.3,c+.3,d-.3),_nether_bridges):
            _n_floor(part,(255,153,27),.034)
    _bridge_drawn=[]
    for bridge in _nether_bridges:
        for part in _n_rect_subtract(bridge,_bridge_drawn):
            _n_floor(part,(84,49,41) if bridge==(5,9,-14.8,-12.8) else (71,52,53),.070)
        _bridge_drawn.append(bridge)

    for tag,positions in [
        ('CRIMSON',[(-19,1),(-12,3),(-7,11),(-18,19),(-6,18)]),
        ('WARPED',[(19,1),(12,3),(7,11),(18,18),(6,18)])]:
        stem=(105,29,50) if tag=='CRIMSON' else (22,99,103)
        crown=(179,31,54) if tag=='CRIMSON' else (24,149,132)
        for x,z in positions:
            _n_solid(x,z,.6,2.5,.6,stem)
            add_box(x,2.3,z,2.4,1.0,2.3,crown,unlit=True)
            add_box(x,3.3,z,1.4,.6,1.4,crown,unlit=True)
            add_box(x+.58,2.4,z-.60,.35,.42,.35,(240,186,69),unlit=True)

    for x,z in [(-20,24),(-15,24),(-10,24),(-21,36),(-8,35)]:
        _n_solid(x,z,.65,2.8,.65,(190,179,148))
        add_box(x,2.6,z,2.0,.35,.35,(205,196,164),unlit=True)
    for x,z in [(-18,31),(-6,23),(-12,38)]:
        add_box(x,.02,z,.6,.28,.6,(43,180,221),unlit=True)

    for x,z,h in [(6,21,3),(20,20,4),(22,32,5),(7,36,2.8),(17,39,4.5),
                  (11,30,2.5),(22,12,3.8)]:
        _n_solid(x,z,.95,h,1.1,(49,48,58))
        add_box(x,h-.08,z,1.0,.16,1.15,(86,85,91),unlit=True)

    brick=(56,23,29)
    for x in (-4.2,4.2):
        for z in (22,30,38):
            _n_solid(x,z,1.6,4.3,1.6,brick)
            add_box(x,4.25,z,2.0,.5,2.0,(72,32,40),unlit=True)
        _n_solid(x,25.8,.65,2.2,5.7,brick)
        _n_solid(x,34,.65,2.2,5.8,brick)

    for z in (22,30,38):
        add_box(0,3.6,z,8.5,.7,1.0,brick,unlit=True)
        for x in (-3,-1,1,3):
            add_box(x,4.3,z,.6,.55,.9,(67,28,36),unlit=True)

    black=(39,36,44)
    for x,z,w,h,d in [(-20,-4,1.2,4,7),(-15,-7,10,3.4,1.0),
                       (-17,-.2,6,2.8,1),(-12,-.2,1,1.5,1),
                       (-20,-7,2,5,2)]:
        _n_solid(x,z,w,h,d,black)
    add_box(-20,5,-7,2.3,.5,2.3,(89,71,34),unlit=True)
    for part in _n_rect_subtract((-19,-11,-6,-1),_nether_bridges):
        _n_floor(part,(50,42,46),.08)

    for key,x,z,q,col in [
        ('gold_nuggets',-5,-7,18,(241,191,45)),
        ('gold_nuggets',5,-6,18,(241,191,45)),
        ('gold_nuggets',-17,-3,18,(241,191,45)),
        ('gold_nuggets',-9,7,9,(241,191,45)),
        ('quartz',3,-9,5,(237,225,210)),('quartz',-5,2,5,(237,225,210)),
        ('glowstone_dust',-10,5,6,(246,204,92)),
        ('glowstone_dust',10,5,6,(246,204,92)),
        ('ancient_debris',0,-7,1,(103,75,59)),
        ('ancient_debris',-1,5,1,(103,75,59)),
        ('ancient_debris',1,17,1,(103,75,59)),
        ('ancient_debris',-1,39,1,(103,75,59)),
        ('soul_sand',-6,28,4,(102,80,57)),
        ('soul_sand',-14,33,4,(102,80,57)),
        ('crimson_mushrooms',-5,5,4,(203,40,68)),
        ('crimson_mushrooms',-15,10,4,(203,40,68)),
        ('warped_mushrooms',5,5,4,(34,179,150)),
        ('warped_mushrooms',15,10,4,(34,179,150)),
        ('blackstone',-18,-5,6,(61,55,68)),
        ('basalt',6,31,6,(92,91,104))]:
        _n_node(key,x,z,q,col)
    _n_chest(-15,-4,{'gold_nuggets':18,'obsidian':4,'string':3})
    _n_chest(2.2,28,{'blaze_rods':2,'quartz':6,'wither_skulls':1})
    _n_chest(-19,34,{'soul_sand':4,'ender_pearls':2,'glowstone_dust':4})

    for typ,x,z in [('PIGLIN',-12,-3),('ZOMBIFIED_PIGLIN',-6,-2),
                     ('HOGLIN',-14,15),('ZOGLIN',-20,17),
                     ('ENDERMAN',13,14),('BLAZE',2,24),('GHAST',-16,29),
                     ('MAGMA_CUBE',16,30),('WITHER_SKELETON',-2,31),
                     ('WITHER_SKELETON',2,36),('STRIDER',7,-13.8),
                     ('STRIDER',-8,-13.8)]:
        _n_spawn_at(typ,x,z)


def _n_reward(etype):
    fn = globals().get('_reward_for')
    if callable(fn):
        try:
            value = fn({'type':etype})
            if type(value) is int and value >= 0:
                return value
        except (KeyError, TypeError):
            pass
    return _shd_lod_matrix(etype)[0]


def _n_spawn_at(etype,x,z,small=False):
    if etype not in NETHER_ENEMY_ORDER or len(enemies) >= 18:
        return None
    lod=_shd_lod_matrix(etype)
    flying=etype in ('BLAZE','GHAST','WITHER')
    if not flying:
        x,z=resolve_collision(x,z,.48)
    hp=lod[1] * (.38 if small else 1.0)
    heights={'HOGLIN':(.8,1.05),'ZOGLIN':(.8,1.05),'GHAST':(1.2,1.5),
             'MAGMA_CUBE':(.48 if small else .72,.43 if small else .80),
             'STRIDER':(.9,.68),'ENDERMAN':(1.7,.8),'WITHER':(1.35,1.6)}
    hit_y,hit_radius=heights.get(etype,(1.25,.72))
    en={'type':etype,'name':_nether_names[etype],'_b_val':_n_reward(etype),
        'x':x,'z':z,'_v_cur':hp,'_v_lim':hp,'speed':random.uniform(*lod[2]),
        'anim':random.uniform(0,math.tau),'strafe_seed':random.uniform(0,math.tau),
        'hit_flash':0,'shoot_timer':random.uniform(2,4),'fuse':0.0,
        '_nether':True,'small':small,'split_done':small,'angry':False,
        'last_hp':hp,'gaze_time':0.0,'teleport_timer':3.0,
        'home_x':x,'home_z':z,'hit_y':hit_y,'hit_radius':hit_radius,
        'y_offset':2.3 if etype=='GHAST' else (1.4 if flying else 0.0)}
    if etype=='WITHER':
        en['birth_timer']=3.0
    en['hit_center_y']=en['y_offset']+hit_y
    enemies.append(en)
    register=globals().get('_register_enemy')
    if callable(register):
        register(en)
    return en


def spawn_enemy(force_type=None):
    if active_dimension != 'NETHER':
        return _nether_base_spawn(force_type)
    if force_type is not None and force_type not in NETHER_ENEMY_ORDER:
        return None
    tag=nether_biome_at()[0]
    choices={'WASTES':('PIGLIN','ZOMBIFIED_PIGLIN'),
             'CRIMSON':('HOGLIN','ZOGLIN','PIGLIN'),
             'WARPED':('ENDERMAN','ZOMBIFIED_PIGLIN'),
             'SOUL':('GHAST','WITHER_SKELETON'),
             'BASALT':('MAGMA_CUBE','BLAZE','WITHER_SKELETON')}
    etype=force_type or random.choice(choices[tag])
    if etype=='WITHER':
        return None
    for _ in range(24):
        angle=random.uniform(0,math.tau)
        dist=random.uniform(10,18)
        x=max(-22,min(22,cam_x+math.sin(angle)*dist))
        z=max(-19,min(39,cam_z+math.cos(angle)*dist))
        if math.hypot(x-cam_x,z-cam_z)<8:
            continue
        if is_point_inside_collider(x,z,margin=.7):
            continue
        if etype not in ('GHAST','BLAZE','MAGMA_CUBE','STRIDER') and nether_is_lava(x,z):
            continue
        return _n_spawn_at(etype,x,z)
    return None


def check_warden_boss_trigger():
    if active_dimension == 'OVERWORLD':
        return _nether_base_warden()


def nether_enemy_hurt(en):
    if not en.get('_nether'):
        return
    en['angry']=True
    en['last_hp']=en['_v_cur']
    if en['type']=='ZOMBIFIED_PIGLIN':
        for other in enemies:
            if other['type']=='ZOMBIFIED_PIGLIN' and math.hypot(
                    en['x']-other['x'],en['z']-other['z'])<10:
                other['angry']=True


def _n_add_resource(key,count):
    if key in nether_inventory:
        nether_inventory[key]=min(9999,nether_inventory[key]+max(0,int(count)))


def on_enemy_killed(en):
    global score, nether_kills, nether_wither_defeated, _nether_mounted
    if not en.get('_nether'):
        return _nether_base_killed(en)
    if en.get('_nether_rewarded'):
        return
    en['_nether_rewarded']=True
    nether_enemy_hurt(en)
    nether_kills += 1


    village_score=score
    score=-1
    en['_b_val']=_n_reward(en['type'])
    try:
        _nether_base_killed(en)
    finally:
        score=village_score
    drops={
        'PIGLIN':('gold_nuggets',3),'ZOMBIFIED_PIGLIN':('gold_nuggets',2),
        'HOGLIN':('leather',2),'ZOGLIN':('leather',2),'BLAZE':('blaze_rods',1),
        'GHAST':('glowstone_dust',3),'MAGMA_CUBE':('magma_cream',1),
        'WITHER_SKELETON':('wither_skulls',1),'ENDERMAN':('ender_pearls',1),
        'STRIDER':('string',2),'WITHER':('nether_star',1)}
    key,q=drops[en['type']]
    _n_add_resource(key,q)
    _n_message(NETHER_RESOURCE_NAMES[key]+' +'+str(q),2.2)
    if en is _nether_mounted:
        _nether_mounted=None
    if en['type']=='MAGMA_CUBE' and not en.get('split_done'):
        en['split_done']=True
        for dx in (-.65,.65):
            _n_spawn_at('MAGMA_CUBE',en['x']+dx,en['z'],small=True)
    if en['type']=='WITHER':
        nether_wither_defeated=True
        _n_message('WITHER YENİLDİ! Nether Yıldızı envanterinde.',6)
        spawn_hit_particles(en['x'],en['y_offset']+1,en['z'],
                            (180,220,255),count=24,speed_mult=2,size_mult=2)


def _n_humanoid(body,skin,leg,swing):
    return [(-.16,max(0,swing),0,.21,.75,leg),
            (.16,max(0,-swing),0,.21,.75,leg),
            (0,.75,0,.62,.75,body),(-.40,.82+swing,.04,.18,.60,skin),
            (.40,.82-swing,.04,.18,.60,skin),(0,1.50,.03,.44,.46,skin)]


def get_enemy_polygons(en):
    if en['type'] not in NETHER_ENEMY_ORDER:
        return _nether_base_polygons(en)
    t=en['type']
    angle=math.atan2(cam_x-en['x'],cam_z-en['z'])
    swing=math.sin(en['anim'])*.10
    hit=en['hit_flash']>0
    parts=[]
    if t in ('PIGLIN','ZOMBIFIED_PIGLIN'):
        skin=(214,150,127) if t=='PIGLIN' else (118,149,96)
        body=(102,66,39) if t=='PIGLIN' else (80,78,55)
        parts=_n_humanoid(body,skin,(67,47,37),swing)
        parts += [(-.29,1.76,.05,.17,.24,skin),(.29,1.76,.05,.17,.24,skin),
                  (0,1.57,.10,.26,.15,(244,179,149)),
                  (.50,.88,.09,.09,.95,(227,185,49)),
                  (.50,1.47,.10,.25,.10,(253,220,92)),
                  (0,.76,.07,.62,.12,(177,139,51)),
                  (-.12,1.785,.245,.105,.095,(255,237,205)),
                  (.12,1.785,.245,.105,.095,(255,237,205)),
                  (-.12,1.785,.268,.043,.068,(126,31,37) if t=='ZOMBIFIED_PIGLIN' else (54,38,28)),
                  (.12,1.785,.268,.043,.068,(126,31,37) if t=='ZOMBIFIED_PIGLIN' else (54,38,28)),
                  (-.12,1.84,.25,.14,.035,(70,45,37)),(.12,1.84,.25,.14,.035,(70,45,37)),
                  (0,1.64,.265,.22,.13,(226,131,125)),
                  (-.055,1.645,.282,.025,.035,(95,45,42)),
                  (.055,1.645,.282,.025,.035,(95,45,42)),
                  (-.25,1.57,.20,.095,.15,(246,224,197)),
                  (.25,1.57,.20,.095,.15,(246,224,197)),
                  (-.25,1.49,.205,.075,.065,(123,69,62)),
                  (.25,1.49,.205,.075,.065,(123,69,62))]
    elif t in ('HOGLIN','ZOGLIN'):
        col=(176,109,90) if t=='HOGLIN' else (105,137,90)
        face=(211,147,127) if t=='HOGLIN' else (112,160,98)
        parts=[(0,.42,0,1.40,.75,col),(0,.67,.06,.89,.65,col),
               (-.50,.07,0,.22,.43,col),(.50,.07,0,.22,.43,col),
               (-.57,.61,.10,.15,.65,(236,216,172)),
               (.57,.61,.10,.15,.65,(236,216,172)),
               (0,1.16,.02,.85,.14,(72,49,42)),
               (-.28,.82,.39,.12,.11,(252,224,186)),
               (.28,.82,.39,.12,.11,(252,224,186)),
               (-.28,.82,.42,.055,.075,(42,29,27)),
               (.28,.82,.42,.055,.075,(42,29,27)),
               (-.31,.89,.40,.17,.04,(91,55,47)),
               (.31,.89,.40,.17,.04,(91,55,47)),
               (0,.60,.43,.36,.22,face),
               (-.075,.62,.455,.04,.055,(75,45,39)),
               (.075,.62,.455,.04,.055,(75,45,39)),
               (-.40,.35,.36,.12,.28,(241,222,176)),
               (.40,.35,.36,.12,.28,(241,222,176)),
               (0,.30,.397,.32,.055,(56,34,34))]
        if t=='ZOGLIN':
            parts += [(-.28,.82,.445,.028,.035,(255,51,37)),(.28,.82,.445,.028,.035,(255,51,37))]
    elif t=='BLAZE':
        parts=[(0,.9,0,.5,.5,(244,188,41)),(0,1.2,.08,.32,.08,(255,247,180))]
        for i in range(8):
            a=en['anim']+i*math.tau/8
            parts.append((math.cos(a)*.62,.23+math.sin(a)*.14,
                          math.sin(a)*.16,.115,.68,(243,145+8*(i%2),22)))
        parts += [(-.12,1.02,.275,.095,.12,(255,246,185)),
                  (.12,1.02,.275,.095,.12,(255,246,185)),
                  (-.12,1.02,.30,.045,.075,(65,32,20)),
                  (.12,1.02,.30,.045,.075,(65,32,20)),
                  (-.15,1.10,.28,.13,.035,(163,83,18)),
                  (.15,1.10,.28,.13,.035,(163,83,18)),
                  (0,.83,.29,.18,.055,(156,59,24))]
    elif t=='GHAST':
        parts=[(0,.65,0,2.1,1.9,(229,219,219)),
               (-.42,1.6,.06,.24,.28,(79,59,68)),
               (.42,1.6,.06,.24,.28,(79,59,68)),
               (0,1.0,.07,.42,.35,(122,56,61))]
        for i in range(5):
            parts.append((-.8+i*.4,.02+math.sin(en['anim']+i)*.13,.03,
                          .16,.67,(182,170,179)))
        parts += [(-.43,1.61,.09,.15,.17,(255,246,228)),
                  (.43,1.61,.09,.15,.17,(255,246,228)),
                  (-.42,1.62,.115,.075,.12,(47,35,43)),
                  (.42,1.62,.115,.075,.12,(47,35,43)),
                  (-.48,1.77,.09,.29,.055,(151,136,141)),
                  (.48,1.77,.09,.29,.055,(151,136,141)),
                  (0,1.08,.115,.30,.20,(175,81,96)),
                  (0,1.03,.14,.19,.035,(248,185,183))]
    elif t=='MAGMA_CUBE':
        size=.72 if en.get('small') else 1.4
        parts=[(0,0,0,size,size,(91,29,20)),
               (0,size*.24,.05,size,.13,(255,117,21)),
               (0,size*.58,.05,size,.13,(255,175,31)),
               (-size*.23,size*.68,.08,size*.15,size*.14,(255,223,71)),
               (size*.23,size*.68,.08,size*.15,size*.14,(255,223,71)),
               (-size*.22,size*.72,.12,size*.07,size*.08,(56,25,25)),
               (size*.22,size*.72,.12,size*.07,size*.08,(56,25,25)),
               (0,size*.47,.14,size*.28,size*.055,(47,20,24))]
    elif t=='WITHER_SKELETON':
        parts=_n_humanoid((38,38,43),(51,49,54),(32,32,38),swing)
        parts += [(0,1.73,.08,.30,.09,(149,140,137)),
                  (.51,.75,.12,.09,1.16,(127,131,137)),
                  (-.11,1.78,.25,.09,.11,(219,218,205)),
                  (.11,1.78,.25,.09,.11,(219,218,205)),
                  (-.11,1.78,.28,.047,.07,(28,23,30)),
                  (.11,1.78,.28,.047,.07,(28,23,30)),
                  (0,1.62,.275,.055,.10,(116,107,102)),
                  (0,1.51,.26,.23,.055,(209,206,190)),
                  (-.10,1.51,.285,.035,.045,(57,47,48)),
                  (.10,1.51,.285,.035,.045,(57,47,48))]
    elif t=='ENDERMAN':
        parts=[(-.16,0,0,.13,1.3,(20,16,29)),(.16,0,0,.13,1.3,(20,16,29)),
               (0,1.28,0,.50,.84,(23,18,32)),
               (-.35,.47,.02,.12,1.48,(20,15,28)),
               (.35,.47,.02,.12,1.48,(20,15,28)),
               (0,2.12,.03,.45,.45,(28,19,37)),
               (-.12,2.35,.07,.14,.055,(227,69,249)),
               (.12,2.35,.07,.14,.055,(227,69,249)),
               (-.12,2.35,.10,.072,.030,(255,208,250)),
               (.12,2.35,.10,.072,.030,(255,208,250)),
               (-.12,2.24,.09,.06,.035,(99,35,128)),
               (.12,2.24,.09,.06,.035,(99,35,128))]
    elif t=='STRIDER':
        parts=[(-.26,0,0,.13,.56,(112,32,48)),(.26,0,0,.13,.56,(112,32,48)),
               (0,.55,0,1.1,.74,(162,47,66)),
               (0,1.28,0,.88,.15,(84,49,45)),
               (-.24,.95,.06,.14,.12,(248,201,174)),
               (.24,.95,.06,.14,.12,(248,201,174)),
               (-.24,.95,.09,.07,.075,(42,28,29)),
               (.24,.95,.09,.07,.075,(42,28,29)),
               (0,.77,.38,.28,.12,(104,38,45)),
               (0,.76,.405,.15,.035,(56,25,31))]
        for x in (-.65,.65):
            parts.append((x,.65,.02,.09,.62,(176,139,143)))
    elif t=='WITHER':
        col=(102,99,125) if en.get('birth_timer',0)>0 else (40,38,48)
        parts=[(0,.65,0,.38,1.22,col),(0,1.5,0,2.2,.24,col)]
        for i,x in enumerate((-.86,0,.86)):
            y=1.75 if i==1 else 1.4
            parts += [(x,y,.02,.61,.6,col),
                      (x-.13,y+.35,.07,.10,.08,(210,211,221)),
                      (x+.13,y+.35,.07,.10,.08,(210,211,221)),
                      (x-.13,y+.36,.105,.052,.045,(240,64,57)),
                      (x+.13,y+.36,.105,.052,.045,(240,64,57)),
                      (x,y+.20,.11,.24,.045,(18,17,22))]
    yoff=en.get('y_offset',0.0)
    parts=[(x,y+yoff,z,w,h,(255,112,104) if hit else c)
           for x,y,z,w,h,c in parts]
    return make_billboard_parts(en['x'],en['z'],angle,parts),angle,0.0


def nether_enemy_hitbox(en):
    return en.get('y_offset',0.0)+en.get('hit_y',1.3),en.get('hit_radius',.88)


def _n_damage(amount,reason):
    global damage_flash, screen_shake, gameover_reason, game_state
    if _adm_god or amount <= 0:
        return
    _apply_armor_damage(amount)
    damage_flash=max(damage_flash,5)
    screen_shake=max(screen_shake,2.5)
    if _sys_vit_gauge <= 0:
        if nether_respawn_at_anchor():
            return
        gameover_reason=reason
        game_state=STATE_GAMEOVER


def nether_respawn_at_anchor():
    global _nether_anchor_charges, cam_x, cam_y, cam_z, _sys_vit_gauge
    global _nether_prev_player, _nether_mounted, _nether_burn_clock, _nether_wither_clock
    if active_dimension!='NETHER' or _nether_anchor_charges<=0:
        return False
    _nether_anchor_charges-=1
    cam_x,cam_z=NETHER_ANCHOR[0],NETHER_ANCHOR[1]+1.4
    cam_y=1.75
    _sys_vit_gauge=100.0
    _nether_prev_player=(cam_x,cam_z)
    _nether_mounted=None
    _nether_burn_clock=_nether_wither_clock=0
    _n_clear_transients()
    update_camera_trig()
    _n_message('Doğma çapası seni kurtardı! Kalan şarj: '+str(_nether_anchor_charges),5)
    return True


def _n_move(en,dx,dz,dt,mult=1.0):
    dist=math.hypot(dx,dz)
    if dist<.01:
        return
    step=en['speed']*dt*mult
    x=en['x']+dx/dist*step
    z=en['z']+dz/dist*step
    if en['type'] in ('GHAST','BLAZE','WITHER'):
        en['x'],en['z']=max(-22,min(22,x)),max(-19,min(39,z))
    else:
        nx,nz=resolve_collision(x,z,.45)
        if math.hypot(nx-en['x'],nz-en['z'])<step*.3:
            nx,nz=resolve_collision(en['x']-dz/dist*step,
                                   en['z']+dx/dist*step,.45)
        en['x'],en['z']=nx,nz


def _n_can_see(en):
    y=en.get('y_offset',0)+en.get('hit_y',1.3)
    dx,dy,dz=cam_x-en['x'],cam_y-.2-y,cam_z-en['z']
    dist=math.sqrt(dx*dx+dy*dy+dz*dz)
    if dist<.1:
        return True
    wall,blocked=raycast_world_colliders(en['x'],y,en['z'],
                                        dx/dist,dy/dist,dz/dist,dist)
    return not blocked or wall>=dist-.5


def _n_shoot(en,speed=9.0):
    if len(enemy_arrows)>=24 or not _n_can_see(en):
        return
    y=en.get('y_offset',0)+en.get('hit_y',1.3)
    dx,dy,dz=cam_x-en['x'],cam_y-.2-y,cam_z-en['z']
    dist=max(.1,math.sqrt(dx*dx+dy*dy+dz*dz))

    enemy_arrows.append([en['x'],y,en['z'],dx/dist*speed,dy/dist*speed,
                         dz/dist*speed,4.2,False,en['type']])


def _n_projectiles(dt):
    for arr in enemy_arrows[:]:
        if arr not in enemy_arrows:
            continue
        if len(arr)<9:
            enemy_arrows.remove(arr)
            continue

        steps=max(1,int(math.sqrt(arr[3]**2+arr[4]**2+arr[5]**2)*dt/.24)+1)
        removed=False
        for _ in range(steps):
            arr[0]+=arr[3]*dt/steps
            arr[1]+=arr[4]*dt/steps
            arr[2]+=arr[5]*dt/steps
            if is_point_inside_collider(arr[0],arr[2],arr[1],margin=.09):
                spawn_hit_particles(arr[0],arr[1],arr[2],(246,114,27),count=4)
                enemy_arrows.remove(arr)
                removed=True
                break
            if math.hypot(arr[0]-cam_x,arr[2]-cam_z)<.74 and abs(arr[1]-(cam_y-.2))<.95:
                _n_damage(_shd_lod_matrix(arr[8])[4],arr[8]+' ATIŞIYLA ÖLDÜN!')
                if arr[8]=='WITHER' and arr in enemy_arrows:
                    globals()['_nether_wither_clock']=4.0
                if arr in enemy_arrows:
                    enemy_arrows.remove(arr)
                removed=True
                break
        if not removed:
            arr[6]-=dt
            if arr[6]<=0 or arr[1]<0:
                enemy_arrows.remove(arr)


def update_nether(dt):
    global _nether_time, _nether_spawn_clock, _nether_prev_player
    global _nether_burn_clock, _nether_wither_clock, _nether_mounted
    global cam_x, cam_y, cam_z, FOG_COLOR, GRASS_BG_COLOR
    if active_dimension!='NETHER' or game_state!=STATE_GAME:
        return
    if market_open or _adm_open or nether_inventory_open:
        _nether_prev_player=(cam_x,cam_z)
        return
    dt=max(0.0,min(.05,float(dt)))
    _nether_time+=dt

    if _nether_mounted is not None and _nether_mounted not in enemies:
        _nether_mounted=None
    if _nether_mounted is not None:
        px,pz=_nether_prev_player
        dx,dz=cam_x-px,cam_z-pz
        cam_x,cam_z=resolve_collision(cam_x+dx*.25,cam_z+dz*.25,.58)
        _nether_mounted['x'],_nether_mounted['z']=cam_x,cam_z
        cam_y=2.28
    else:
        cam_y=1.75

        if nether_biome_at()[0]=='SOUL':
            px,pz=_nether_prev_player
            mult=1.30 if _nether_soul_speed else .72
            cam_x,cam_z=resolve_collision(px+(cam_x-px)*mult,
                                          pz+(cam_z-pz)*mult,.58)
    _nether_prev_player=(cam_x,cam_z)
    tag,name,col=nether_biome_at()
    GRASS_BG_COLOR=col
    FOG_COLOR=(44,76,80) if tag in ('SOUL','WARPED') else (91,30,29)
    if _adm_freeze:
        return
    if nether_is_lava(cam_x,cam_z) and _nether_mounted is None:
        _nether_burn_clock=1.8
        _n_damage(21.0*dt,'LAVDA YANDIN!')
    elif _nether_burn_clock>0:
        _nether_burn_clock=max(0,_nether_burn_clock-dt)
        _n_damage(3.0*dt,'LAV ATEŞİYLE ÖLDÜN!')
    if _nether_wither_clock>0:
        _nether_wither_clock=max(0,_nether_wither_clock-dt)
        _n_damage(4.0*dt,'WITHER ETKİSİYLE ÖLDÜN!')
    _n_projectiles(dt)
    _nether_spawn_clock+=dt
    if _nether_spawn_clock>=6.0:
        _nether_spawn_clock=0

        if len(enemies)<16:
            spawn_enemy()
    for en in enemies[:]:
        if not en.get('_nether'):
            continue
        if en['_v_cur']<en.get('last_hp',en['_v_cur']):
            nether_enemy_hurt(en)
        en['last_hp']=en['_v_cur']
        en['hit_flash']=max(0,en['hit_flash']-1)
        en['anim']+=dt*6.0
        t=en['type']
        dx,dz=cam_x-en['x'],cam_z-en['z']
        dist=math.hypot(dx,dz)
        if t=='STRIDER':
            if en is not _nether_mounted:

                _n_move(en,en['home_x']-en['x'],en['home_z']-en['z'],dt,.35)
            continue
        hostile=True
        if t=='PIGLIN':
            hostile=en['angry'] or armor_level!=3
        elif t=='ZOMBIFIED_PIGLIN':
            hostile=en['angry']
        elif t=='ENDERMAN':
            y=en['hit_y']+en.get('y_offset',0)
            vy=y-cam_y
            length=max(.01,math.sqrt(dx*dx+dz*dz+vy*vy))

            gaze=(-dx*math.sin(cam_yaw)*math.cos(cam_pitch)
                  -dz*math.cos(cam_yaw)*math.cos(cam_pitch)
                  +vy*math.sin(cam_pitch))/length
            if dist<17 and gaze>.985 and _n_can_see(en):
                en['gaze_time']+=dt
                if en['gaze_time']>.45 and not en['angry']:
                    en['angry']=True
                    _n_message('Enderman göz teması yüzünden öfkelendi!')
            else:
                en['gaze_time']=max(0,en['gaze_time']-dt*2)
            hostile=en['angry']
            en['teleport_timer']-=dt
            if hostile and en['teleport_timer']<=0 and dist>4:
                en['teleport_timer']=4
                a=random.uniform(0,math.tau)
                x,z=cam_x+math.sin(a)*5,cam_z+math.cos(a)*5
                if -22<x<22 and -19<z<39 and not nether_is_lava(x,z) and not is_point_inside_collider(x,z,margin=.8):
                    spawn_hit_particles(en['x'],2,en['z'],(192,61,233),count=6)
                    en['x'],en['z']=x,z
                    dx,dz=cam_x-x,cam_z-z
                    dist=math.hypot(dx,dz)
        if not hostile:
            _n_move(en,en['home_x']-en['x'],en['home_z']-en['z'],dt,.25)
            continue
        if t in ('BLAZE','GHAST','WITHER'):
            baseline=2.3 if t=='GHAST' else 1.4
            en['y_offset']=baseline+math.sin(en['anim']*.45)*.32
            if t=='WITHER' and en.get('birth_timer',0)>0:
                en['birth_timer']=max(0,en['birth_timer']-dt)
                continue
        if t=='MAGMA_CUBE':
            en['y_offset']=max(0,math.sin(en['anim']*1.6))*(.25 if en['small'] else .50)
        en['hit_center_y']=en.get('y_offset',0)+en['hit_y']
        ranged=t in ('BLAZE','GHAST','WITHER') or (t=='PIGLIN' and dist>3)
        if ranged and dist<27:
            en['shoot_timer']-=dt
            if en['shoot_timer']<=0:
                en['shoot_timer']=1.35 if t=='WITHER' else (3.6 if t=='GHAST' else 2.6)
                _n_shoot(en,10 if t=='WITHER' else (7.5 if t=='GHAST' else 11))
        stop=9 if ranged else (1.6 if t in ('HOGLIN','ZOGLIN') else 1.2)
        if dist>stop:
            _n_move(en,dx,dz,dt)
        elif ranged and dist<5:
            _n_move(en,-dx,-dz,dt,.6)
        elif not ranged:
            _n_damage(_shd_lod_matrix(t)[3]*dt,
                      _nether_names[t].upper()+' TARAFINDAN ÖLDÜRÜLDÜN!')
            if t=='WITHER_SKELETON':
                _nether_wither_clock=3.5
    update_camera_trig()


def get_nether_portal_world_pos():
    return NETHER_RETURN_PORTAL if active_dimension=='NETHER' else NETHER_OVERWORLD_PORTAL


def update_nether_portal_screen_rect(shake_x=0,shake_y=0):
    global nether_portal_screen_rect
    nether_portal_screen_rect=pygame.Rect(0,0,0,0)
    if game_state!=STATE_GAME:
        return
    x,z=get_nether_portal_world_pos()
    pc=world_to_camera(x,1.35,z)
    if not NEAR_PLANE<pc[2]<FAR_PLANE:
        return
    distance=math.hypot(x-cam_x,z-cam_z)
    wall,blocked=raycast_world_colliders(cam_x,cam_y,cam_z,
                  (x-cam_x)/max(.01,distance),0,(z-cam_z)/max(.01,distance),distance)
    if blocked and wall<distance-.7:
        return
    sx,sy=project_point(*pc)
    w=max(24,int(1.65/pc[2]*FOV))
    h=max(44,int(2.8/pc[2]*FOV))
    nether_portal_screen_rect=pygame.Rect(sx-w//2+shake_x,sy-h//2+shake_y,w,h).clip(
        pygame.Rect(0,0,WIDTH,VIEW_H))


def get_nether_portal_polygons():
    if game_state!=STATE_GAME:
        return []
    update_nether_portal_screen_rect()
    x,z=get_nether_portal_world_pos()
    angle=math.atan2(cam_x-x,cam_z-z)
    unlocked=active_dimension=='NETHER' or nether_portal_unlocked()
    pulse=int((math.sin(pygame.time.get_ticks()*.005)+1)*22)
    inner=(82,22,143+pulse) if unlocked else (34,24,39)
    parts=[(0,.12,0,1.15,2.45,inner),(-.72,0,.03,.28,2.85,(28,21,38)),
           (.72,0,.03,.28,2.85,(28,21,38)),(0,2.60,.03,1.7,.25,(28,21,38)),
           (0,0,.03,1.7,.25,(28,21,38))]
    if unlocked:
        parts += [(-.72,.12,.05,.08,2.46,(173,71,232)),
                  (.72,.12,.05,.08,2.46,(173,71,232))]
    return make_billboard_parts(x,z,angle,parts)


def get_nether_glow_points():
    if active_dimension!='NETHER':
        return []
    return [(a+(b-a)*.5,c+(d-c)*.5) for a,b,c,d in _nether_lava]


def get_nether_extra_polygons():
    if active_dimension!='NETHER':
        return []
    out=[]
    for node in _nether_nodes:
        if not node['mined'] and math.hypot(node['x']-cam_x,node['z']-cam_z)<27:
            out.extend(node['polygons'])
    for chest in _nether_chests:
        if not chest['opened'] and math.hypot(chest['x']-cam_x,chest['z']-cam_z)<27:
            out.extend(chest['polygons'])
    for x,z,col in [(NETHER_ANCHOR[0],NETHER_ANCHOR[1],(77,39,105)),
                    (NETHER_LODESTONE[0],NETHER_LODESTONE[1],(103,114,121))]:
        if math.hypot(x-cam_x,z-cam_z)<27:
            out.extend(_n_box(x,.02,z,.9,.7,.9,col))
    if _nether_anchor_charges:
        out.extend(_n_box(NETHER_ANCHOR[0],.70,NETHER_ANCHOR[1],.66,.10,.66,(230,170,65)))
    ax,az=NETHER_ALTAR
    if math.hypot(ax-cam_x,az-cam_z)<27:
        for x,y in [(ax-.8,.6),(ax,.6),(ax+.8,.6),(ax,0)]:
            out.extend(_n_box(x,y,az,.70,.60,.70,(87,66,49)))
        if not _nether_boss_summoned:
            for x in (ax-.8,ax,ax+.8):
                out.extend(_n_box(x,1.2,az,.38,.38,.38,(55,51,59)))
    for arr in enemy_arrows:
        if len(arr)>8:
            t=arr[8]
            col=(73,54,83) if t=='WITHER' else (255,137,31)
            angle=math.atan2(cam_x-arr[0],cam_z-arr[2])
            size=.36 if t in ('GHAST','WITHER') else .18
            out.extend(make_billboard_parts(arr[0],arr[2],angle,
                [(0,arr[1]-size/2,0,size,size,col)]))
    return out


def _n_context():
    if _nether_mounted is not None:
        return 'DISMOUNT',_nether_mounted,'STRIDER: İN'
    x,z=get_nether_portal_world_pos()
    if math.hypot(x-cam_x,z-cam_z)<3.4:
        return 'PORTAL',None,('KÖYE DÖN' if active_dimension=='NETHER' else 'NETHER: GİR')
    if active_dimension!='NETHER':
        return '',None,'ETKİLEŞ'
    candidates=[]
    for target,action,label in [(NETHER_ANCHOR,'ANCHOR','ÇAPA: ŞARJ ET (4 IŞIKTAŞI)'),
                                (NETHER_LODESTONE,'LODESTONE','MIKNATIS TAŞINA BAĞLAN')]:
        d=math.hypot(target[0]-cam_x,target[1]-cam_z)
        if d<2.1:
            candidates.append((d,action,None,label))
    for node in _nether_nodes:
        d=math.hypot(node['x']-cam_x,node['z']-cam_z)
        if not node['mined'] and d<2.1:
            candidates.append((d,'MINE',node,'KAZ: '+NETHER_RESOURCE_NAMES[node['key']]))
    for chest in _nether_chests:
        d=math.hypot(chest['x']-cam_x,chest['z']-cam_z)
        if not chest['opened'] and d<2.1:
            candidates.append((d,'CHEST',chest,'SANDIĞI AÇ'))
    for en in enemies:
        d=math.hypot(en['x']-cam_x,en['z']-cam_z)
        if d<2.4 and en['type']=='STRIDER':
            candidates.append((d,'MOUNT',en,'STRIDER: BİN'))
        if d<2.4 and en['type']=='PIGLIN' and not en['angry'] and armor_level==3:
            candidates.append((d,'BARTER',en,'TAKAS: 9 ALTIN PARÇASI'))
    d=math.hypot(cam_x-NETHER_ALTAR[0],cam_z-NETHER_ALTAR[1])
    if d<3:
        candidates.append((d,'SUMMON',None,'WITHER ÇAĞIR: 3 KAFA + 4 KUM'))
    if candidates:
        _,action,obj,label=min(candidates,key=lambda item:item[0])
        return action,obj,label
    return '',None,'YAKLAŞ: KAYNAK / PİGLİN / STRIDER'


def _n_pay(cost):
    if any(nether_inventory.get(k,0)<v for k,v in cost.items()):
        return False
    for k,v in cost.items():
        nether_inventory[k]-=v
    return True


def nether_craft(action):
    global armor_level, _sys_vit_gauge, _nether_burn_clock
    global _nether_soul_speed
    if action=='INGOT':
        if not _n_pay({'ancient_debris':4,'gold_nuggets':36}):
            _n_message('Külçe eksik. Antik kalıntı: '+str(nether_inventory['ancient_debris'])+'/4 • Altın: '+str(nether_inventory['gold_nuggets'])+'/36.',5)
            return False
        _n_add_resource('netherite_ingots',1)
        _n_message('Netherit külçesi üretildi. Elmas zırhı yükseltebilirsin.')
        return True
    if action=='ARMOR':
        if armor_level!=4:
            _n_message('Önce marketten elmas zırh kuşan (seviye 4).')
            return False
        if not _n_pay({'netherite_ingots':1}):
            _n_message('Yükseltme için 1 netherit külçesi gerekir.')
            return False
        armor_level=5
        _n_message('Elmas zırhın NETHERİT zırha yükseltildi!')
        return True
    if action=='STEW':
        if _sys_vit_gauge>=100:
            _n_message('Canın zaten tam; mantar harcanmadı.')
            return False
        if not _n_pay({'crimson_mushrooms':2,'warped_mushrooms':2}):
            _n_message('Çorba için 2 kızıl + 2 çarpık mantar gerekir.')
            return False
        _sys_vit_gauge=min(100.0,_sys_vit_gauge+25.0)
        _n_message('Mantar çorbası: +25 can.')
        return True
    if action=='SOUL':
        if _nether_soul_speed:
            _n_message('Ruh Hızı zaten üretildi; kaynak harcanmadı.')
            return False
        if not _n_pay({'ender_pearls':3,'quartz':3}):
            _n_message('Ruh Hızı için 3 inci + 3 kuvars gerekir.')
            return False
        _nether_soul_speed=True
        _n_message('Ruh Hızı üretildi! Ruh kumunda artık hızlı yürürsün.')
        return True
    if action=='FIRE':
        if not _n_pay({'magma_cream':2,'blaze_rods':1}):
            _n_message('Ateşi söndürmek için 2 magma kremi + 1 blaze çubuğu.')
            return False
        _nether_burn_clock=0
        _n_message('Üzerindeki ateş söndü; lavda kalırsan yeniden yanarsın.')
        return True
    return False


def summon_nether_wither():
    global _nether_boss_summoned
    if active_dimension!='NETHER' or math.hypot(
            cam_x-NETHER_ALTAR[0],cam_z-NETHER_ALTAR[1])>3:
        _n_message('Kalenin sonundaki çağırma altarına yaklaş (z=34).')
        return False
    if _nether_boss_summoned:
        _n_message('Bu dünyanın Wither çağrısı zaten kullanıldı.')
        return False
    if len(enemies)>=18:
        _n_message('Altar kalabalık; önce birkaç yaratığı temizle.')
        return False
    if not _n_pay({'wither_skulls':3,'soul_sand':4}):
        _n_message('Wither için 3 iskelet kafası + 4 ruh kumu gerekir.',4)
        return False
    boss=_n_spawn_at('WITHER',0,35.8)
    if boss is None:
        _n_add_resource('wither_skulls',3)
        _n_add_resource('soul_sand',4)
        return False
    _nether_boss_summoned=True
    _n_message('WITHER ÇAĞRILDI! Üç başlı boss 3 saniye sonra saldırır.',5)
    return True


def nether_interact():
    global _nether_mounted, cam_x, cam_z, cam_y, _nether_prev_player
    global _nether_anchor_charges, _nether_lodestone_bound
    if game_state!=STATE_GAME or market_open or _adm_open or nether_inventory_open:
        return False
    action,obj,label=_n_context()
    if action=='PORTAL':
        return leave_nether() if active_dimension=='NETHER' else enter_nether()
    if action=='DISMOUNT':

        for radius in (1.3,2.5,4.0):
            for i in range(12):
                a=i*math.tau/12
                x,z=cam_x+math.sin(a)*radius,cam_z+math.cos(a)*radius
                if -23<x<23 and -20<z<40 and not nether_is_lava(x,z) and not is_point_inside_collider(x,z,margin=.65):
                    _nether_mounted=None
                    cam_x,cam_z,cam_y=x,z,1.75
                    _nether_prev_player=(x,z)
                    _n_message('Strider’dan güvenli zemine indin.')
                    return True
        _n_message('Lav ortasındasın; önce kıyıya veya köprüye git.')
        return False
    if action=='MOUNT':
        _nether_mounted=obj
        obj['home_x'],obj['home_z']=obj['x'],obj['z']
        _nether_prev_player=(cam_x,cam_z)
        cam_y=2.28
        _n_message('Strider: yön tuşlarıyla lavı güvenle geç; ETKİLEŞ ile in.')
        return True
    if action=='MINE':
        obj['mined']=True
        _n_add_resource(obj['key'],obj['quantity'])
        _n_message(NETHER_RESOURCE_NAMES[obj['key']]+' +'+str(obj['quantity']))
        return True
    if action=='CHEST':
        obj['opened']=True
        for k,v in obj['loot'].items():
            _n_add_resource(k,v)
        _n_message('Sandık ganimeti envantere eklendi; sandık artık boş.')
        return True
    if action=='BARTER':
        if not _n_pay({'gold_nuggets':9}):
            _n_message('Takas için 9 altın parçası (1 külçe) gerekir.')
            return False
        k,q=random.choice([('ender_pearls',2),('quartz',5),('obsidian',3),
                           ('glowstone_dust',4),('string',4),('soul_sand',3),
                           ('warped_mushrooms',3)])
        _n_add_resource(k,q)
        _n_message('Piglin takası: '+NETHER_RESOURCE_NAMES[k]+' +'+str(q))
        return True
    if action=='SUMMON':
        return summon_nether_wither()
    if action=='ANCHOR':
        if _nether_anchor_charges>=4:
            _n_message('Çapanın şarjı tam (4).')
            return False
        if not _n_pay({'glowstone_dust':4}):
            _n_message('Bir çapa şarjı için 4 ışıktaşı tozu gerekir.')
            return False
        _nether_anchor_charges+=1
        _n_message('Doğma çapası aktif: '+str(_nether_anchor_charges)+' kez yeniden doğabilirsin.')
        return True
    if action=='LODESTONE':
        _nether_lodestone_bound=True
        _n_message('Mıknatıs taşına bağlandın; pusula HUD’da görünür.')
        return True
    _n_message('Yakındaki cevher, sandık, altar veya Strider ile etkileş.')
    return False


def nether_handle_tap(tx,ty):
    """True = bu dokunma tüketildi; ateş/kamera hareketine yönlendirme."""
    global nether_inventory_open, _nether_touch_cooldown
    if game_state!=STATE_GAME or market_open or _adm_open:
        return False
    if nether_inventory_open:
        if _nether_close_rect.collidepoint(tx,ty):
            nether_inventory_open=False
            _n_clear_input()
        else:
            for rect,recipe in zip(_nether_recipe_rects,('INGOT','ARMOR','STEW','SOUL')):
                if rect.collidepoint(tx,ty):
                    nether_craft(recipe)
                    break
        return True
    if nether_inventory_rect.collidepoint(tx,ty):
        nether_inventory_open=True
        _n_clear_input()
        return True
    hit_portal=(nether_portal_screen_rect.width>0 and
                nether_portal_screen_rect.inflate(18,18).collidepoint(tx,ty))
    if nether_action_rect.collidepoint(tx,ty) or hit_portal:
        now=pygame.time.get_ticks()
        if now<_nether_touch_cooldown:
            return True
        _nether_touch_cooldown=now+260
        if hit_portal:
            x,z=get_nether_portal_world_pos()
            if math.hypot(x-cam_x,z-cam_z)>4.5:
                _n_message('Geçmek için portala yaklaş.')
            else:
                leave_nether() if active_dimension=='NETHER' else enter_nether()
        else:
            nether_interact()
        return True
    return False


def _n_clear_input():
    active_touches.clear()
    touch_roles.clear()
    touch_last_pos.clear()


def _n_button(rect,label,color=(103,52,119)):
    pygame.draw.rect(screen,color,rect,border_radius=7)
    pygame.draw.rect(screen,(213,160,236),rect,1,border_radius=7)
    draw_text_fit(label,font_small,(250,240,255),rect.centerx,rect.centery,rect.width-8)


def draw_nether_hud():
    if game_state!=STATE_GAME or market_open or _adm_open:
        return
    _n_button(nether_inventory_rect,'ÇANTA / ÜRET')
    action,obj,label=_n_context()
    _n_button(nether_action_rect,label,(106,47,69) if action else (58,43,54))
    if active_dimension=='NETHER':
        biome=nether_biome_at()[1]
        draw_text_fit(biome+' • Nether leş: '+str(nether_kills),font_small,
                      (255,198,151),int(WIDTH*.33),int(HEIGHT*.076),int(WIDTH*.62))
        debris=[node for node in _nether_nodes if node['key']=='ancient_debris' and not node['mined']]
        if debris:
            nearest=min(debris,key=lambda node:math.hypot(node['x']-cam_x,node['z']-cam_z))
            dist=math.hypot(nearest['x']-cam_x,nearest['z']-cam_z)
            draw_text_fit('Netherit kalıntısı: '+str(int(dist))+' m • ALTIN DAMARI',font_small,
                          (255,210,113),int(WIDTH*.66),int(HEIGHT*.195),int(WIDTH*.63))
        if _nether_lodestone_bound:
            dx,dz=NETHER_LODESTONE[0]-cam_x,NETHER_LODESTONE[1]-cam_z
            delta=(math.atan2(dx,dz)-cam_yaw+math.pi)%math.tau-math.pi
            direction='ÖNDE' if abs(delta)<.55 else ('ARKADA' if abs(delta)>2.5 else ('SAĞDA' if delta>0 else 'SOLDA'))
            draw_text_fit('Mıknatıs: '+str(int(math.hypot(dx,dz)))+'m '+direction,
                          font_small,(174,202,222),int(WIDTH*.48),int(HEIGHT*.165),int(WIDTH*.28))
        boss=next((e for e in enemies if e['type']=='WITHER'),None)
        if boss:
            rect=pygame.Rect(int(WIDTH*.06),int(HEIGHT*.195),int(WIDTH*.88),int(HEIGHT*.035))
            pygame.draw.rect(screen,(32,25,43),rect)
            ratio=max(0,min(1,boss['_v_cur']/max(.1,boss['_v_lim'])))
            pygame.draw.rect(screen,(158,80,186),(rect.x,rect.y,int(rect.width*ratio),rect.height))
            draw_text_fit('WITHER '+str(int(max(0,boss['_v_cur'])))+'/'+str(int(boss['_v_lim'])),
                          font_small,(255,245,255),rect.centerx,rect.centery,rect.width-8)
        if _nether_burn_clock>0 or _nether_wither_clock>0:
            warn='LAV / ATEŞ' if _nether_burn_clock>0 else 'WITHER ETKİSİ'
            draw_text_fit(warn,font_small,(255,104,77),WIDTH//2,int(HEIGHT*.245),int(WIDTH*.8))
    elif not nether_portal_unlocked():
        draw_text_fit('Nether: silah + köyde 10 leş',font_small,(204,156,224),
                      int(WIDTH*.33),int(HEIGHT*.18),int(WIDTH*.63))
    if nether_portal_screen_rect.width>0:
        label='NETHER • KÖYE DÖN' if active_dimension=='NETHER' else (
              'NETHER • GİR' if nether_portal_unlocked() else 'NETHER • KİLİTLİ')
        draw_text_fit(label,font_small,(227,168,252),nether_portal_screen_rect.centerx,
                      max(int(HEIGHT*.24),nether_portal_screen_rect.y-9),int(WIDTH*.7))
    if pygame.time.get_ticks()<_nether_message_until:
        rect=pygame.Rect(int(WIDTH*.03),VIEW_H-int(HEIGHT*.046),int(WIDTH*.94),int(HEIGHT*.038))
        pygame.draw.rect(screen,(37,20,40),rect,border_radius=6)
        draw_text_fit(_nether_message,font_small,(255,220,177),rect.centerx,rect.centery,rect.width-10)
    if not nether_inventory_open:
        return

    pygame.draw.rect(screen,(26,20,31),_nether_panel,border_radius=10)
    pygame.draw.rect(screen,(180,112,197),_nether_panel,2,border_radius=10)
    draw_text_fit('NETHER ÇANTASI — TAŞINABİLİR',font_ui,(249,208,255),
                  WIDTH//2,int(HEIGHT*.213),int(WIDTH*.86))
    items=list(NETHER_RESOURCE_NAMES.items())
    for i,(key,name) in enumerate(items):
        col=i//9
        row=i%9
        cx=int(WIDTH*(.265 if col==0 else .735))
        y=int(HEIGHT*(.244+row*.027))
        draw_text_fit(name+': '+str(nether_inventory[key]),font_small,(220,205,224),
                      cx,y,int(WIDTH*.425))
    labels=['KÜLÇE ÜRET • 4 antik kalıntı + 36 altın',
            'Elmas zırh → Netherit: 1 külçe',
            'Çorba +25 can: 2 kızıl + 2 çarpık mantar',
            'Ruh Hızı: 3 ender incisi + 3 kuvars']
    for rect,label in zip(_nether_recipe_rects,labels):
        _n_button(rect,label,(71,44,81))
    draw_text_fit('Altın çizgili kızıl cevher = Antik Kalıntı • Altın zırh Piglin’i sakinleştirir',font_small,
                  (223,177,120),WIDTH//2,int(HEIGHT*.652),int(WIDTH*.88))
    _n_button(_nether_close_rect,'KAPAT')



import queue

GAME_VERSION = "4.1 • NETHER REMASTER"
paused = False
help_open = False
quality_mode = "DENGELİ"
QUALITY_ORDER = ("ULTRA", "DENGELİ", "ORTA", "PİL DOSTU")
QUALITY_PROFILES = {"ULTRA": (60, 42.0, 170, True), "DENGELİ": (60, 32.0, 110, False), "ORTA": (45, 29.0, 90, False), "PİL DOSTU": (30, 27.0, 64, False)}
MAX_PARTICLES = 110
QUALITY_GLOW = False
look_sensitivity = 1.0
hitmarker_time = 0.0
pause_rect = pygame.Rect(int(WIDTH*.67), int(HEIGHT*.945), int(WIDTH*.30), int(HEIGHT*.043))
help_rect = pygame.Rect(int(WIDTH*.03), int(HEIGHT*.945), int(WIDTH*.48), int(HEIGHT*.043))
_pause_rows = [pygame.Rect(int(WIDTH*.10), int(HEIGHT*(.27+i*.085)), int(WIDTH*.80), int(HEIGHT*.07)) for i in range(6)]
_net_queue = queue.Queue(maxsize=8)
_remote_last_fire = 0.0
_remote_last_packet = 0.0


def apply_quality_profile(mode):
    global quality_mode, TARGET_FPS, FAR_PLANE, MAX_PARTICLES, QUALITY_GLOW
    if mode not in QUALITY_PROFILES:
        mode = "DENGELİ"
    quality_mode = mode
    TARGET_FPS, FAR_PLANE, MAX_PARTICLES, QUALITY_GLOW = QUALITY_PROFILES[mode]
    return mode


def _clear_controls():
    active_touches.clear()
    touch_roles.clear()
    touch_last_pos.clear()


def _panel(rect, fill=(17, 22, 32), edge=(99, 130, 151), radius=12):
    pygame.draw.rect(screen, (5, 7, 13), rect.move(0, 3), border_radius=radius)
    pygame.draw.rect(screen, fill, rect, border_radius=radius)
    pygame.draw.rect(screen, edge, rect, 1, border_radius=radius)


def draw_updated_menu():
    screen.fill((10, 9, 19))
    for y in range(HEIGHT):
        t = y / float(HEIGHT)
        pygame.draw.line(screen, (int(15+27*t), int(12+6*t), int(29+13*t)), (0,y), (WIDTH,y))
    tick = pygame.time.get_ticks()*.001
    for i in range(30):
        x = int((i*47 + math.sin(tick*.4+i)*17) % WIDTH)
        y = int((HEIGHT-i*59-tick*(8+i%5)) % HEIGHT)
        pygame.draw.rect(screen, (125+i%3*28, 50+i%4*11, 34), (x,y,2,3))

    frame = pygame.Rect(int(WIDTH*.35), int(HEIGHT*.065), int(WIDTH*.30), int(HEIGHT*.17))
    pygame.draw.rect(screen, (111, 54, 175), frame.inflate(14,14), border_radius=8)
    pygame.draw.rect(screen, (34, 24, 48), frame.inflate(8,8), 7, border_radius=4)
    pygame.draw.rect(screen, (65, 22, 100), frame)
    for i in range(7):
        yy = frame.y+int((i*17+tick*18)%frame.height)
        pygame.draw.line(screen, (117+i%2*28,43,165+i%2*35), (frame.x+4,yy), (frame.right-4,yy), 3)
    draw_text_fit("MİNECRAFT KÖYÜ", font_title, (244,232,206), WIDTH//2, int(HEIGHT*.285), int(WIDTH*.91))
    draw_text_fit("NETHER REMASTER  /  4.1", font_ui, (214,149,255), WIDTH//2, int(HEIGHT*.337), int(WIDTH*.87))
    _panel(singleplayer_btn_rect, (45,91,72), (115,218,171))
    draw_text_fit("TEK KİŞİLİK MACERA", font_btn, (244,255,247), singleplayer_btn_rect.centerx, singleplayer_btn_rect.centery, singleplayer_btn_rect.width-18)
    _panel(multiplayer_btn_rect, (30,47,63), (99,150,190))
    draw_text_fit("KÖY CO-OP  •  BETA", font_ui, (199,233,255), multiplayer_btn_rect.centerx, multiplayer_btn_rect.centery, multiplayer_btn_rect.width-16)
    draw_text_fit("5 biyom • Takas • Netherit • Wither", font_small, (224,178,136), WIDTH//2, int(HEIGHT*.69), int(WIDTH*.91))
    draw_text_fit("Nether: tek kişilik / Köy & End korunur", font_small, (160,167,185), WIDTH//2, int(HEIGHT*.735), int(WIDTH*.93))
    draw_text_fit("Yapımcı: YouTube viruscodes", font_ui, (212,211,201), WIDTH//2, int(HEIGHT*.87), int(WIDTH*.90))
    draw_text_fit("Pydroid 3 • Pygame • Harici dosyasız", font_small, (133,145,161), WIDTH//2, int(HEIGHT*.92), int(WIDTH*.88))


def toggle_pause():
    global paused, help_open
    if game_state not in (STATE_GAME, STATE_END):
        return
    paused = not paused
    help_open = False
    _clear_controls()


def draw_pause_menu():
    screen.set_clip(None)
    screen.fill((12,13,24))
    draw_text_fit("DURAKLATILDI", font_title, (243,220,189), WIDTH//2, int(HEIGHT*.16), int(WIDTH*.89))
    draw_text_fit("Çok oyunculuda bağlantı sürer", font_small, (171,188,207), WIDTH//2, int(HEIGHT*.215), int(WIDTH*.86))
    labels = ["OYUNA DEVAM", "KONTROLLER / NETHER REHBERİ", "GRAFİK: "+quality_mode, "KAMERA HASSASİYETİ: "+("DÜŞÜK" if look_sensitivity < 1 else "NORMAL" if look_sensitivity == 1 else "YÜKSEK"), "ANA MENÜYE DÖN", "OYUNU KAPAT"]
    for i, r in enumerate(_pause_rows):
        _panel(r, (30,48,54) if i == 0 else (26,27,43), (97,157,141) if i == 0 else (105,87,129))
        draw_text_fit(labels[i], font_ui, (229,234,235), r.centerx, r.centery, r.width-12)
    draw_text_fit("Ana menüye dönüş mevcut turu bitirir.", font_small, (181,155,142), WIDTH//2, int(HEIGHT*.84), int(WIDTH*.93))
    if help_open:
        r = pygame.Rect(int(WIDTH*.035), int(HEIGHT*.11), int(WIDTH*.93), int(HEIGHT*.79))
        _panel(r, (17,23,31), (159,113,204))
        lines = ["KONTROLLER / NETHER", "Sol tuşlar: yürü • Ekranı sürükle: bak", "Ateş tuşu: ateş • Otomatik silah: basılı tut", "Dedeye dokun: ücretsiz tabancayı al", "10 köy yaratığı yen: Nether portalı açılır", "Portal yaklaşınca GİR / DÖN düğmesi", "ETKİLEŞ: maden, sandık, takas, Strider", "ÇANTA: eşyalar, üretim ve Nether rehberi", "Piglin: altın zırhla barış / altınla takas", "Lava tehlikeli! Strider ile geçebilirsin", "Netherit: kızıl-altın kalıntı x4; Çanta → Külçe üret", "Wither: 3 kafatası + 4 ruh kumu", "Klavye: WASD, J/L bak, U/O yukarı/aşağı", "SPACE ateş • E etkileş • R silah • P duraklat", "Kapatmak için rehbere tekrar dokun"]
        for i, text in enumerate(lines):
            draw_text_fit(text, font_ui if i==0 else font_small, (222,173,255) if i==0 else (218,226,230), WIDTH//2, r.y+22+i*int(HEIGHT*.047), r.width-14)


def _pause_tap(tx, ty):
    global paused, help_open, quality_mode, TARGET_FPS, FAR_PLANE, look_sensitivity, game_state, running
    if help_open:
        help_open = False
        return
    for i, r in enumerate(_pause_rows):
        if not r.collidepoint(tx,ty):
            continue
        if i == 0: paused = False
        elif i == 1: help_open = True
        elif i == 2:
            apply_quality_profile(QUALITY_ORDER[(QUALITY_ORDER.index(quality_mode)+1)%len(QUALITY_ORDER)])
        elif i == 3:
            look_sensitivity = .7 if look_sensitivity > 1 else 1.0 if look_sensitivity < 1 else 1.35
        elif i == 4:
            _stop_network_session()
            reset_game()
            game_state = STATE_MENU
            paused = False
        elif i == 5: running = False
        _clear_controls()
        return


def draw_update_controls():
    if game_state not in (STATE_GAME, STATE_END):
        return
    _panel(pause_rect, (28,34,45), (113,132,157), 6)
    draw_text_fit("DURAKLAT", font_small, (222,232,243), pause_rect.centerx, pause_rect.centery, pause_rect.width-6)
    _panel(help_rect, (28,34,45), (113,132,157), 6)
    draw_text_fit("4.1 NETHER  /  REHBER", font_small, (222,232,243), help_rect.centerx, help_rect.centery, help_rect.width-6)
    if hitmarker_time > 0 and not market_open and not _adm_open:
        for sx, sy in ((-1,-1),(-1,1),(1,-1),(1,1)):
            pygame.draw.line(screen,(255,226,156),(CENTER_X+sx*5,CENTER_Y+sy*5),(CENTER_X+sx*10,CENTER_Y+sy*10),2)


apply_quality_profile(quality_mode)
_original_ui_tap = process_menu_or_ui_tap

def process_menu_or_ui_tap(tx, ty):
    global paused, help_open
    if paused:
        _pause_tap(tx,ty)
        return True
    if game_state in (STATE_GAME, STATE_END):
        if pause_rect.collidepoint(tx,ty):
            toggle_pause()
            return True
        if help_rect.collidepoint(tx,ty):
            paused = True
            help_open = True
            _clear_controls()
            return True

        if market_open:
            return handle_market_click(tx,ty)
        if _adm_open:
            return handle_admin_click(tx,ty)
        if nether_inventory_open:
            return nether_handle_tap(tx,ty)
        market_rect = end_market_btn_rect if game_state == STATE_END else market_btn_rect
        admin_rect = end_admin_btn_rect if game_state == STATE_END else admin_hud_btn_rect
        if has_gun and market_rect.collidepoint(tx,ty):
            if net_mode == "CLIENT":
                _nether_notice("Co-op marketini oda sahibi yönetir.")
            else:
                globals()["market_open"] = True
                _clear_controls()
            return True
        if has_gun and _adm_unlocked and admin_rect.collidepoint(tx,ty):
            globals()["_adm_open"] = True
            _clear_controls()
            return True
        if game_state == STATE_GAME and nether_handle_tap(tx,ty):
            _clear_controls()
            return True
        end_hit = end_portal_screen_rect.width > 0 and end_portal_screen_rect.inflate(34,28).collidepoint(tx,ty)
        if (game_mode == "MULTI" or net_mode is not None) and game_state == STATE_GAME and end_portal_unlocked and end_hit:
            _nether_notice("End savaşı bu sürümde tek kişilik oynanır.")
            return True
    return _original_ui_tap(tx,ty)


_original_fire = fire_weapon

def fire_weapon():
    global hitmarker_time
    if paused or nether_inventory_open or not _verify_gl_integrity() or not _adm_state_valid():
        return
    if current_weapon not in owned_weapons:
        return
    before = sum(max(0, e.get("_v_cur",0)) for e in enemies)+end_dragon_hp+sum(end_crystal_hp)
    _original_fire()
    after = sum(max(0, e.get("_v_cur",0)) for e in enemies)+end_dragon_hp+sum(end_crystal_hp)
    if after < before:
        hitmarker_time = .16


def _finite_field(value, low, high):
    if isinstance(value, bool) or not isinstance(value,(int,float)) or not math.isfinite(value):
        raise ValueError("Geçersiz ağ sayısı")
    if not low <= value <= high:
        raise ValueError("Ağ sayısı sınır dışında")
    return value


def _parse_incoming_stream(recv_buf):
    """Ağ thread'i dünya listelerine dokunmaz; ana döngü doğrulanmış kuyruğu uygular."""
    if len(recv_buf) > 262144:
        return ""
    lines = recv_buf.split("\n")
    for line in lines[:-1]:
        if len(line) > 65536:
            continue
        pkt = _verify_packet(line.strip(),input_pin_text)
        if not pkt or pkt.get("protocol") != NETWORK_PROTOCOL:
            continue
        try:
            clean = {"x":float(_finite_field(pkt.get("x"),-24,24)), "z":float(_finite_field(pkt.get("z"),-21,41.5)), "yaw":float(_finite_field(pkt.get("yaw"),-1000,1000)) % math.tau, "pitch":float(_finite_field(pkt.get("pitch"),-1.2,1.2)), "moving":bool(pkt.get("moving")), "weapon":pkt.get("weapon","NONE"), "shoot_seq":int(_finite_field(pkt.get("shoot_seq",0),0,2147483647))}
            if clean["weapon"] not in set(WEAPONS)|{"NONE"}: continue
            clean["money"] = 0
            if net_mode == "HOST":
                clean["weapon"] = "PISTOL" if clean["weapon"] != "NONE" else "NONE"
            if net_mode == "CLIENT" and "world_seq" in pkt:
                seq = int(_finite_field(pkt["world_seq"],0,2147483647))
                inc = pkt.get("enemies",[])
                if not isinstance(inc,list) or len(inc)>32: continue
                validated=[]
                for e in inc:
                    if not isinstance(e,dict) or e.get("type") not in tuple(_eco_defs["enemies"]): continue
                    typ=e["type"]; stats=_shd_lod_matrix(typ)
                    v={"type":typ,"name":ENEMY_TYPES[typ]["name"],"_b_val":stats[0]}
                    for key,lo,hi,default in (("x",-24,24,0),("z",-21,41.5,0),("_v_cur",0,5000,1),("_v_lim",1.5,5000,2),("speed",0,10,2),("anim",-1e8,1e8,0),("strafe_seed",-10,10,0),("hit_flash",0,120,0),("shoot_timer",-10,20,2),("fuse",0,3,0)):
                        v[key]=float(_finite_field(e.get(key,default),lo,hi))
                    validated.append(v)
                arrs=pkt.get("arrows",[])
                if not isinstance(arrs,list) or len(arrs)>128: continue
                valid_arr=[]
                for a in arrs:
                    if not isinstance(a,list) or len(a) not in (7,8): continue
                    vals=[float(_finite_field(a[k],-10000,10000)) for k in range(7)]
                    valid_arr.append(vals+[bool(a[7]) if len(a)>7 else False])
                clean.update(world_seq=seq,enemies=validated,arrows=valid_arr,score=int(_finite_field(pkt.get("score",0),0,999999)),hp=float(_finite_field(pkt.get("hp",100),0,100)),money=int(_finite_field(pkt.get("money",0),0,9999999)),warden_active=bool(pkt.get("warden_active")),warden_defeated=bool(pkt.get("warden_defeated")),portal_unlocked=bool(pkt.get("portal_unlocked")))
            if _net_queue.full():
                try: _net_queue.get_nowait()
                except queue.Empty: pass
            _net_queue.put_nowait(clean)
        except (ValueError,TypeError,OverflowError,queue.Full):
            continue
    return lines[-1]


def _drain_network_packets():
    global _network_last_world_seq, score, _sys_vit_gauge, warden_active, warden_defeated, end_portal_unlocked, _remote_last_packet
    if _remote_last_packet and time.monotonic()-_remote_last_packet > 3.0:
        remote_player_pos["active"] = False
    while True:
        try: pkt=_net_queue.get_nowait()
        except queue.Empty: break
        now=time.monotonic()
        if net_mode == "HOST" and remote_player_pos.get("active"):
            allowance = max(.25,min(2.0,now-_remote_last_packet))*8.0+1.0
            if math.hypot(pkt["x"]-remote_player_target["x"],pkt["z"]-remote_player_target["z"])>allowance:
                pkt["x"],pkt["z"]=remote_player_target["x"],remote_player_target["z"]
        if net_mode == "HOST" and remote_player_pos.get("active"):
            pkt["shoot_seq"] = max(remote_player_target["shoot_seq"], pkt["shoot_seq"])
        _remote_last_packet=now
        remote_player_target.update({k:pkt[k] for k in ("x","z","yaw","pitch","weapon","money","moving","shoot_seq")})
        if net_mode == "CLIENT" and pkt.get("world_seq",-1)>_network_last_world_seq:
            _network_last_world_seq=pkt["world_seq"]
            enemies[:]=pkt["enemies"]
            enemy_arrows[:]=pkt["arrows"]
            score=pkt["score"]
            _sys_vit_gauge=pkt["hp"]
            _rt_wallet.host_sync(pkt["money"])
            warden_active=pkt["warden_active"]
            warden_defeated=pkt["warden_defeated"]
            end_portal_unlocked=pkt["portal_unlocked"]
        if not remote_player_pos["active"]:
            remote_player_pos.update(remote_player_target)
            remote_player_pos["active"]=True


def _server_apply_remote_shot():
    global _remote_last_fire
    if net_mode != "HOST" or not remote_player_pos.get("active") or paused:
        return

    weapon=remote_player_target.get("weapon")
    if weapon != "PISTOL" or not _verify_gl_integrity(): return
    now=time.monotonic()
    if now-_remote_last_fire < _gl_wep_shader(weapon)[1]/60.0*.95: return
    _remote_last_fire=now
    yaw,pitch=remote_player_target["yaw"],remote_player_target["pitch"]
    origin=(remote_player_target["x"],1.75,remote_player_target["z"])
    direction=(math.sin(yaw)*math.cos(pitch),math.sin(pitch),math.cos(yaw)*math.cos(pitch))
    wall,_=raycast_world_colliders(*origin,*direction,30.0)
    target,closest=None,wall
    for en in enemies:
        center=(en["x"],1.85 if en["type"]=="WARDEN" else 1.25,en["z"])
        r=1.0 if en["type"]=="WARDEN" else .5
        t=_ray_ellipsoid_distance(origin,direction,center,(r,1.4 if en["type"]=="WARDEN" else 1.0,r))
        if t is not None and t<closest: target,closest=en,t
    if target is not None:
        target["_v_cur"]-=_gl_wep_shader(weapon)[2]
        target["hit_flash"]=6
        spawn_hit_particles(target["x"],1.35,target["z"],(255,95,65),count=6)
        if target["_v_cur"]<=0 and target in enemies:
            enemies.remove(target)
            on_enemy_killed(target)


_original_stop_network = _stop_network_session

def _stop_network_session():
    global _remote_last_fire, _remote_last_packet
    _original_stop_network()
    _remote_last_fire=_remote_last_packet=0.0
    while True:
        try: _net_queue.get_nowait()
        except queue.Empty: break


_base_armor_damage = _apply_armor_damage

def _apply_armor_damage(amount):

    if net_mode == "CLIENT": return 0.0
    return _base_armor_damage(amount)


def _draw_vital_bars():
    if market_open or _adm_open: return
    r=pygame.Rect(int(WIDTH*.03),int(HEIGHT*.072),int(WIDTH*.61),int(HEIGHT*.022))
    _panel(r,(32,21,30),(87,49,57),5)
    fill=int(max(0,min(100,_sys_vit_gauge))/100.0*(r.width-4))
    if fill>0: pygame.draw.rect(screen,(94,198,142) if _sys_vit_gauge>35 else (241,99,91),(r.x+2,r.y+2,fill,r.height-4),border_radius=3)
    draw_text_fit(f"{int(_sys_vit_gauge)} HP  •  {armor_names[armor_level]}",font_small,(231,239,241),r.centerx,int(HEIGHT*.112),r.width)


_original_reset_all = reset_game

def reset_game():
    global paused, help_open, hitmarker_time, spawn_timer, shoot_cooldown, recoil_offset, armor_level, market_tab
    reset_nether()
    _original_reset_all()
    paused=help_open=False
    hitmarker_time=0.0
    spawn_timer=shoot_cooldown=0
    recoil_offset=0.0
    armor_level=0
    market_tab="weapons"
    _clear_controls()


def raycast_world_colliders(sx, sy, sz, dx, dy, dz, max_dist):
    """Üç eksende tam kutu kesişimi; duvarın üstünden/altından yanlış isabet yok."""
    closest=max_dist
    hit=False
    for x1,x2,z1,z2,max_y in world_colliders:
        t=_ray_aabb_distance((sx,sy,sz),(dx,dy,dz),((x1,x2),(0.0,max_y),(z1,z2)))
        if t is not None and .05<t<closest:
            closest=t
            hit=True
    if dy < -1e-8:
        t=-sy/dy
        if .05<t<closest: closest,hit=t,True
    return closest,hit


def _nether_notice(text):
    global dialog_active, dialog_speaker, dialog_text, dialog_timer
    dialog_active = True
    dialog_speaker = "NETHER / BİLGİ"
    dialog_text = str(text)
    dialog_timer = 220

_ENEMY_ORDER_FOR_DIGEST = tuple(dict.fromkeys(_ENEMY_ORDER_FOR_DIGEST + NETHER_ENEMY_ORDER))
_init_economy_seals()

reset_game()

running = True
while running:
    dt = min(0.05, clock.tick(TARGET_FPS) / 1000.0)

    _now_ms = pygame.time.get_ticks()
    if _now_ms - _integrity_last_check_ms >= 750:
        _integrity_last_check_ms = _now_ms
        _verify_gl_integrity()
        _adm_state_valid()
        _rt_wallet.get()

    if ui_click_cooldown > 0:
        ui_click_cooldown = max(0.0, ui_click_cooldown-dt*60.0)

    if game_mode == "MULTI" and remote_player_pos["active"]:
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
            if net_mode == "HOST":
                _server_apply_remote_shot()
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

        elif event.type == getattr(pygame, "WINDOWFOCUSLOST", -900):
            _clear_controls()
            if game_state in (STATE_GAME, STATE_END):
                paused = True
        elif event.type == pygame.KEYDOWN:
            if event.key in (pygame.K_ESCAPE, pygame.K_p, getattr(pygame,"K_AC_BACK",-901)):
                if game_state in (STATE_GAME, STATE_END):
                    toggle_pause()
                elif game_state != STATE_MENU:
                    _stop_network_session()
                    game_state = STATE_MENU
                else:
                    running = False
            elif not paused and not nether_inventory_open and game_state in (STATE_GAME, STATE_END):
                if event.key == pygame.K_SPACE:
                    fire_weapon()
                elif event.key == pygame.K_e and game_state == STATE_GAME:
                    nether_interact()
                elif event.key == pygame.K_m and has_gun and net_mode != "CLIENT":
                    market_open = not market_open
                    _clear_controls()
                elif event.key == pygame.K_r and has_gun:
                    ordered = [w for w in WEAPON_ORDER + ["ADMIN_GUN"] if w in owned_weapons]
                    current_weapon = ordered[(ordered.index(current_weapon)+1)%len(ordered)] if current_weapon in ordered else "PISTOL"
        elif event.type == pygame.FINGERDOWN:
            using_touch_device = True
            tx, ty = int(event.x * WIDTH), int(event.y * HEIGHT)
            fid = event.finger_id
            active_touches[fid] = (tx, ty)
            touch_last_pos[fid] = (tx, ty)

            if pause_rect.collidepoint(tx, ty) or help_rect.collidepoint(tx, ty) or paused:
                touch_roles[fid] = "UI"
                process_menu_or_ui_tap(tx, ty)
            elif game_state == STATE_END:
                if market_open or _adm_open or end_market_btn_rect.collidepoint(tx, ty) or (_adm_unlocked and end_admin_btn_rect.collidepoint(tx, ty)):
                    touch_roles[fid] = "UI"
                    process_menu_or_ui_tap(tx, ty)
                elif math.hypot(tx - shoot_btn_center[0], ty - shoot_btn_center[1]) <= shoot_btn_radius * 1.25:
                    touch_roles[fid] = "SHOOT"
                    fire_weapon()
                elif is_in_dpad_area(tx, ty):
                    touch_roles[fid] = "MOVE"
                elif ty < VIEW_H:
                    touch_roles[fid] = "LOOK"
                else:
                    touch_roles[fid] = "MOVE"
            elif game_state != STATE_GAME or market_open or _adm_open:
                touch_roles[fid] = "UI"
                process_menu_or_ui_tap(tx, ty)
            else:
                if (has_gun and market_btn_rect.collidepoint(tx, ty)) or (
                    has_gun and _adm_unlocked and admin_hud_btn_rect.collidepoint(tx, ty)
                ):
                    touch_roles[fid] = "UI"
                    process_menu_or_ui_tap(tx, ty)
                elif nether_handle_tap(tx, ty):
                    touch_roles[fid] = "UI"
                    _clear_controls()
                elif active_dimension == "OVERWORLD" and game_mode != "MULTI" and net_mode is None and end_portal_unlocked and end_portal_screen_rect.width > 0 and end_portal_screen_rect.inflate(34, 28).collidepoint(tx, ty):
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
            if paused:
                continue
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

            if not paused and game_state in (STATE_GAME, STATE_END) and not market_open and not _adm_open and not nether_inventory_open:
                if touch_roles.get(fid) == "LOOK":
                    lx, ly = touch_last_pos.get(fid, (tx, ty))
                    dx = tx - lx
                    dy = ty - ly
                    if game_state == STATE_END:
                        end_cam_yaw = (end_cam_yaw + dx * 0.0075 * look_sensitivity) % (math.pi * 2.0)
                        end_cam_pitch = max(-.9, min(1.05, end_cam_pitch - dy * 0.0065 * look_sensitivity))
                    else:
                        cam_yaw = (cam_yaw + dx * 0.0075 * look_sensitivity) % (math.pi * 2.0)
                        cam_pitch = max(-.9, min(1.05, cam_pitch - dy * 0.0065 * look_sensitivity))

            touch_last_pos[fid] = (tx, ty)

        elif event.type == pygame.FINGERUP:
            fid = event.finger_id
            active_touches.pop(fid, None)
            touch_roles.pop(fid, None)
            touch_last_pos.pop(fid, None)

        elif event.type == pygame.MOUSEBUTTONDOWN and not using_touch_device:
            mx, my = event.pos
            if paused:
                _pause_tap(mx, my)
            elif game_state == STATE_END:
                if not process_menu_or_ui_tap(mx, my):
                    if math.hypot(mx - shoot_btn_center[0], my - shoot_btn_center[1]) <= shoot_btn_radius * 1.25:
                        fire_weapon()
            elif game_state != STATE_GAME or market_open or _adm_open:
                process_menu_or_ui_tap(mx, my)
            else:
                if not process_menu_or_ui_tap(mx, my):
                    if is_in_shoot_area(mx, my):
                        fire_weapon()
                    else:
                        check_old_man_interaction(mx, my)

        elif event.type == pygame.MOUSEMOTION and not using_touch_device:
            if not paused and pygame.mouse.get_pressed()[0] and game_state in (STATE_GAME, STATE_END) and not market_open and not _adm_open and not nether_inventory_open:
                mx, my = event.pos
                if my < VIEW_H and not is_in_dpad_area(mx, my) and not is_in_shoot_area(mx, my):
                    dx, dy = event.rel
                    if game_state == STATE_END:
                        end_cam_yaw = (end_cam_yaw + dx * 0.0075 * look_sensitivity) % (math.pi * 2.0)
                        end_cam_pitch = max(-.9, min(1.05, end_cam_pitch - dy * 0.0065 * look_sensitivity))
                    else:
                        cam_yaw = (cam_yaw + dx * 0.0075 * look_sensitivity) % (math.pi * 2.0)
                        cam_pitch = max(-.9, min(1.05, cam_pitch - dy * 0.0065 * look_sensitivity))

    _drain_network_packets()
    hitmarker_time = max(0.0, hitmarker_time-dt)
    if paused:
        draw_pause_menu()
        pygame.display.flip()
        continue
    if not paused and game_state in (STATE_GAME, STATE_END) and not market_open and not _adm_open and not nether_inventory_open:
        keys_look = pygame.key.get_pressed()
        look_delta = (float(keys_look[pygame.K_l])-float(keys_look[pygame.K_j]))*dt*1.5*look_sensitivity
        pitch_delta = (float(keys_look[pygame.K_u])-float(keys_look[pygame.K_o]))*dt*1.1*look_sensitivity
        if game_state == STATE_END:
            end_cam_yaw = (end_cam_yaw+look_delta)%math.tau
            end_cam_pitch = max(-.9,min(1.05,end_cam_pitch+pitch_delta))
        else:
            cam_yaw = (cam_yaw+look_delta)%math.tau
            cam_pitch = max(-.9,min(1.05,cam_pitch+pitch_delta))
    if game_state == STATE_END:

        if not market_open and not _adm_open and not nether_inventory_open:
            move_f, move_s = 0.0, 0.0
            firing_held = False
            end_points = list(active_touches.values())
            if not using_touch_device and pygame.mouse.get_pressed()[0]:
                end_points.append(pygame.mouse.get_pos())
            for tx, ty in end_points:
                if btn_up.collidepoint(tx, ty): move_f += 1.0
                if btn_down.collidepoint(tx, ty): move_f -= 1.0
                if btn_left.collidepoint(tx, ty): move_s -= 1.0
                if btn_right.collidepoint(tx, ty): move_s += 1.0
                if is_in_shoot_area(tx, ty): firing_held = True
            keys = pygame.key.get_pressed()
            if keys[pygame.K_w] or keys[pygame.K_UP]: move_f += 1.0
            if keys[pygame.K_s] or keys[pygame.K_DOWN]: move_f -= 1.0
            if keys[pygame.K_a] or keys[pygame.K_LEFT]: move_s -= 1.0
            if keys[pygame.K_d] or keys[pygame.K_RIGHT]: move_s += 1.0
            if firing_held and (_gl_wep_shader(current_weapon)[3] or _adm_hyper) and shoot_cooldown <= 0:
                fire_end_weapon()
            old_x, old_z = end_cam_x, end_cam_z
            if move_f or move_s:
                mag = math.hypot(move_f, move_s)
                move_f /= mag
                move_s /= mag
                speed = (11.5 if _adm_hyper else 5.4) * dt
                nx = end_cam_x + (math.sin(end_cam_yaw)*move_f + math.cos(end_cam_yaw)*move_s) * speed
                nz = end_cam_z + (math.cos(end_cam_yaw)*move_f - math.sin(end_cam_yaw)*move_s) * speed
                nx = max(-10.45, min(10.45, nx))
                nz = max(6.35, min(37.65, nz))
                end_cam_x, end_cam_z = nx, nz
            if dt > 0.0001:
                end_player_vx = (end_cam_x - old_x) / dt
                end_player_vz = (end_cam_z - old_z) / dt
            else:
                end_player_vx = end_player_vz = 0.0
            try:
                _update_end_fireballs(dt)
            except Exception as end_update_error:

                print("END GÜNCELLEME HATASI:", repr(end_update_error))
                end_fireballs.clear()
                end_player_vx = end_player_vz = 0.0
                screen.fill((12, 7, 25))
                draw_text_fit("END SAVAŞI GÜNCELLENİRKEN HATA", font_ui,
                              (255, 150, 130), WIDTH//2, int(HEIGHT*0.42),
                              int(WIDTH*0.92))
                draw_text_fit(str(end_update_error)[:48], font_small,
                              (245, 220, 220), WIDTH//2, int(HEIGHT*0.49),
                              int(WIDTH*0.90))
                pygame.display.flip()
                continue
        if shoot_cooldown > 0:
            shoot_cooldown = max(0.0, shoot_cooldown-dt*60.0)
        if recoil_offset > 0.0:
            recoil_offset = max(0.0, recoil_offset - dt * 6.8)
        if damage_flash > 0:
            damage_flash = max(0, damage_flash - dt*60.0)
        try:
            draw_end_dimension(dt)
        except Exception as end_draw_error:

            print("END SAHNE HATASI:", repr(end_draw_error))
            screen.fill((12, 7, 25))
            draw_text_fit("END SAHNESİ YÜKLENİRKEN HATA", font_ui, (255,120,120),
                          WIDTH//2, int(HEIGHT*0.42), int(WIDTH*0.92))
            draw_text_fit(str(end_draw_error)[:48], font_small, (245,220,220),
                          WIDTH//2, int(HEIGHT*0.49), int(WIDTH*0.90))
        draw_update_controls()
        try:
            pygame.display.flip()
        except Exception as end_flip_error:
            print("END EKRAN HATASI:", repr(end_flip_error))
            game_state = STATE_GAME
            end_fireballs.clear()
        continue

    if game_state == STATE_WIN:
        screen.fill((0, 0, 0))
        elapsed = max(0, pygame.time.get_ticks() - end_credits_start)
        credits = ["MINECRAFT KÖYÜ: THE END", "", "Yapımcı: viruscodes", "Oyun Admini: Efe", "", "Ender Ejderhası yenildi.", "Köy artık güvende.", "", "OYNADIĞINIZ İÇİN TEŞEKKÜRLER!", "", "Bu macerada bizimle olduğun için teşekkürler."]
        for i, line in enumerate(credits):
            y = HEIGHT + 35 + i * 52 - int(elapsed * 0.035)
            if -40 < y < HEIGHT + 40:
                draw_text_fit(line, font_btn if i in (0, 2, 3, 8) else font_ui, (235,235,235), WIDTH//2, y, int(WIDTH*.88))
        if elapsed > 18000:
            pygame.draw.rect(screen, (35, 160, 65), play_btn_rect, border_radius=14)
            draw_text_fit("YENİDEN OYNA", font_btn, (255,255,255), play_btn_rect.centerx, play_btn_rect.centery, play_btn_rect.width-12)
        pygame.display.flip()
        continue

    if game_state == STATE_MENU:
        draw_updated_menu()
        pygame.display.flip()
        continue

    if game_state == STATE_MULTIPLAYER_MENU:
        screen.fill((12, 25, 38))
        pygame.draw.rect(screen, (22, 60, 75), (0, int(HEIGHT * 0.63), WIDTH, int(HEIGHT * 0.37)))
        draw_text_fit("MULTIPLAYER", font_title, (90, 245, 255), WIDTH // 2, int(HEIGHT * 0.15), int(WIDTH * 0.88))
        draw_text_fit("BETA SÜRÜMÜ", font_btn, (255, 215, 90), WIDTH // 2, int(HEIGHT * 0.23), int(WIDTH * 0.82))

        pygame.draw.rect(screen, (28, 112, 170), host_btn_rect, border_radius=12)
        pygame.draw.rect(screen, (155, 225, 255), host_btn_rect, 2, border_radius=12)
        draw_text_fit("ODA KUR", font_btn, (255, 255, 255), host_btn_rect.centerx, host_btn_rect.centery, host_btn_rect.width - 18)

        pygame.draw.rect(screen, (35, 125, 75), join_btn_rect, border_radius=12)
        pygame.draw.rect(screen, (175, 255, 195), join_btn_rect, 2, border_radius=12)
        draw_text_fit("ODAYA KATIL", font_btn, (255, 255, 255), join_btn_rect.centerx, join_btn_rect.centery, join_btn_rect.width - 18)

        pygame.draw.rect(screen, (70, 75, 85), mp_back_btn_rect, border_radius=10)
        pygame.draw.rect(screen, (185, 195, 210), mp_back_btn_rect, 2, border_radius=10)
        draw_text_fit("GERİ", font_ui, (255, 255, 255), mp_back_btn_rect.centerx, mp_back_btn_rect.centery, mp_back_btn_rect.width - 12)
        pygame.display.flip()
        continue

    if game_state in (STATE_HOST_PIN, STATE_JOIN_PIN):
        screen.fill((20, 30, 50))
        draw_text_fit("ODA BAĞLANTI PANELİ", font_btn, (255, 225, 75), WIDTH // 2, int(HEIGHT * 0.08), int(WIDTH * 0.88))

        if game_state == STATE_HOST_PIN:
            host_ip_label = host_public_ip if host_public_ip else get_local_ip()
            draw_text_fit(f"IP: {host_ip_label}  |  PORT: {pin_to_port(input_pin_text)}", font_small, (150, 220, 255), WIDTH // 2, int(HEIGHT * 0.16), int(WIDTH * 0.92))
            draw_text_fit(network_mapping_status if host_public_ip else "İnternet için UPnP veya yönlendiricide TCP port yönlendirme gerekir", font_small, (255, 205, 130), WIDTH // 2, int(HEIGHT * 0.195), int(WIDTH * 0.94))
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

            draw_text_fit("2. Arkadaşının IP Adresi:", font_small, (200, 220, 255), WIDTH // 2, int(HEIGHT * 0.33), int(WIDTH * 0.88))
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

    if not market_open and not _adm_open and not nether_inventory_open:
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
            shoot_cooldown = max(0.0, shoot_cooldown-dt*60.0)
        if recoil_offset > 0.0:
            recoil_offset = max(0.0, recoil_offset - dt * 6.8)
        if muzzle_light > 0.0:
            muzzle_light = max(0.0, muzzle_light - dt * 11.0)
        if damage_flash > 0:
            damage_flash = max(0.0, damage_flash-dt*60.0)
        if dialog_active and dialog_timer > 0 and troll_state == "NORMAL":
            dialog_timer -= dt*60.0
            if dialog_timer <= 0:
                dialog_active = False

        for tr in tracers[:]:
            tr[2] -= dt * 8.0
            if tr[2] <= 0.0:
                tracers.remove(tr)
        if len(tracers) > 72:
            del tracers[:-72]

        for p in particles[:]:
            p[0] += p[3] * dt
            p[1] += p[4] * dt
            p[2] += p[5] * dt
            p[4] -= 9.8 * dt
            p[7] -= dt
            if p[7] <= 0.0 or p[1] < 0.0:
                particles.remove(p)
        if len(particles) > MAX_PARTICLES:
            del particles[:-MAX_PARTICLES]

        if active_dimension == "NETHER":
            update_nether(dt)
        for arr in (enemy_arrows[:] if active_dimension == "OVERWORLD" else []):
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
                    _apply_armor_damage(dmg)
                    damage_flash = 8 if is_sonic else 6
                    screen_shake = 7.5 if is_sonic else 4.2
                enemy_arrows.remove(arr)
                if _sys_vit_gauge <= 0 and not _adm_god:
                    gameover_reason = "WARDEN SONİK PATLAMASIYLA ÖLDÜN!" if is_sonic else "İSKELET OKUYLA VURULDUN!"
                    game_state = STATE_GAMEOVER
            elif arr[6] <= 0.0 or arr[1] <= 0.0:
                enemy_arrows.remove(arr)

        if troll_state == "CATCH" and not _dede_eliminated:
            troll_timer -= dt*60.0
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

        if active_dimension == "OVERWORLD" and has_gun and troll_state == "NORMAL" and net_mode != "CLIENT":
            if not warden_active and not _adm_freeze:
                spawn_timer += dt*60.0
                max_en = 6 if not warden_defeated else 8
                spawn_interval = 72 if not warden_defeated else 52
                if spawn_timer >= spawn_interval and len(enemies) < max_en:
                    spawn_timer = 0
                    spawn_enemy()

            for i, en in enumerate(enemies[:]):
                if en["hit_flash"] > 0:
                    en["hit_flash"] = max(0.0, en["hit_flash"]-dt*60.0)
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
                                _apply_armor_damage(_lod[3] * dmg_ratio)
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
                        _apply_armor_damage(dps * dt)
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
    if active_dimension == "OVERWORLD" and sun_y < horizon_clamped - 10:
        pygame.draw.rect(screen, (255, 235, 140), (sun_x - 22, sun_y - 22, 44, 44))
        pygame.draw.rect(screen, (255, 255, 220), (sun_x - 16, sun_y - 16, 32, 32))

    for sx, sy, sr, _ in sky_dots:
        dot_x = int((sx - cam_yaw * 140) % WIDTH)
        dot_y = (sy + pitch_shift) % max(1, VIEW_H)
        if 0 <= dot_y < horizon_clamped - 8:
            dot_col = (247, 131, 73) if active_dimension == "NETHER" else (230,240,255)
            pygame.draw.rect(screen, dot_col, (dot_x, dot_y, sr, sr))

    render_list = []

    def queue_polygons(poly_list):
        for poly in poly_list:
            verts, col, unlit, center, layer_bias = poly[:5]
            poly_radius = poly[5] if len(poly) > 5 else 2.0

            cdx = center[0] - cam_x
            cdz = center[2] - cam_z
            if cdx * cdx + cdz * cdz > (FAR_PLANE + poly_radius) ** 2:
                continue



            center_cam = world_to_camera(center[0], center[1], center[2])
            if center_cam[2] + poly_radius < NEAR_PLANE:
                continue
            if center_cam[2] - poly_radius > FAR_PLANE:
                continue
            if center_cam[2] > 0.0 and abs(center_cam[0]) > center_cam[2] * 0.58 + poly_radius * 1.35:
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

            render_list.append((avg_z + layer_bias, "POLY", proj_pts, draw_col))

    queue_polygons(world_polygons)
    queue_polygons(get_nether_portal_polygons())
    update_nether_portal_screen_rect(shake_ox, shake_oy)
    if active_dimension == "NETHER":
        queue_polygons(get_nether_extra_polygons())
        if QUALITY_GLOW:
            for glow_x, glow_z in get_nether_glow_points():
                glow_cam = world_to_camera(glow_x, .08, glow_z)
                if NEAR_PLANE < glow_cam[2] < FAR_PLANE:
                    glow_xy = project_point(*glow_cam)
                    glow_radius = max(3, min(64, int((1.25/glow_cam[2])*FOV)))
                    render_list.append((glow_cam[2]-.12, "LAVA_GLOW", (glow_xy[0]+shake_ox,glow_xy[1]+shake_oy), glow_radius))
    if active_dimension == "OVERWORLD" and end_portal_unlocked:
        queue_polygons(get_end_portal_polygons())
        portal_x, portal_z = get_end_portal_world_pos()
        portal_cam = world_to_camera(portal_x, 1.30, portal_z)
        if NEAR_PLANE < portal_cam[2] < FAR_PLANE:
            portal_sx, portal_sy = project_point(portal_cam[0], portal_cam[1], portal_cam[2])
            portal_w = max(24, int((1.55 / portal_cam[2]) * FOV))
            portal_h = max(45, int((2.75 / portal_cam[2]) * FOV))
            portal_box = pygame.Rect(portal_sx - portal_w // 2 + shake_ox,
                                     portal_sy - portal_h // 2 + shake_oy,
                                     portal_w, portal_h)
            end_portal_screen_rect = portal_box.clip(pygame.Rect(0, 0, WIDTH, VIEW_H))
        else:
            end_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
    else:
        end_portal_screen_rect = pygame.Rect(0, 0, 0, 0)
    om_polys, om_angle = get_old_man_polygons()
    queue_polygons(om_polys)

    rp_polys, rp_angle = get_remote_player_polygons()
    queue_polygons(rp_polys)

    om_cam = world_to_camera(troll_pos[0], 1.0, troll_pos[2])
    if active_dimension == "OVERWORLD" and om_cam[2] > NEAR_PLANE and not _dede_eliminated:
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
            if en["type"] not in NETHER_ENEMY_ORDER and en["type"] != "WARDEN":
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
        elif rtype == "LAVA_GLOW":
            pygame.draw.circle(screen,(105,42,25),data,extra,2)
            pygame.draw.circle(screen,(174,71,28),data,max(2,extra//2),1)
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


    if game_mode == "MULTI" and remote_player_pos["active"]:
        rcam = world_to_camera(remote_player_pos["x"], 2.35, remote_player_pos["z"])
        if NEAR_PLANE < rcam[2] < FAR_PLANE:
            rsx, rsy = project_point(rcam[0], rcam[1], rcam[2])
            rw_name = WEAPONS.get(remote_player_pos["weapon"], {"name": "Silahsız"})["name"]
            draw_text_fit(f"[ AGA - {rw_name} ]", font_small, (80, 230, 255), rsx, rsy - 10, int(WIDTH * 0.65))

    if active_dimension == "OVERWORLD" and NEAR_PLANE < om_cam[2] < 9.5 and troll_state == "NORMAL" and not _dede_eliminated:
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
    if armor_level > 0 and (active_dimension == "NETHER" or game_mode == "MULTI" or warden_active):
        draw_text_fit(f"ZIRH: {armor_names[armor_level].upper()}", font_small,
                      (205, 220, 255), int(WIDTH*.33), int(HEIGHT*.110), int(WIDTH*.61))
    draw_text_fit(
        f"CAN: %{'SONSUZ' if _adm_god else hp_int}  |  LEŞ: {score}  |  PARA: ${_rt_wallet.get()}",
        font_ui, (255, 245, 190), WIDTH // 2, int(HEIGHT * 0.031), int(WIDTH * 0.94)
    )


    if game_mode == "MULTI":

        aga_box = pygame.Rect(int(WIDTH * 0.03), int(HEIGHT * 0.072), int(WIDTH * 0.62), int(HEIGHT * 0.052))
        pygame.draw.rect(screen, (16, 34, 52), aga_box, border_radius=8)
        pygame.draw.rect(screen, (80, 210, 255), aga_box, 2, border_radius=8)
        if remote_player_pos["active"]:
            aga_txt = f"BETA • Diğer Oyuncu: ${remote_player_pos['money']}"
        elif net_mode == "HOST":
            aga_txt = (f"Katıl: {host_public_ip}:{pin_to_port(input_pin_text)}"
                       if host_public_ip else network_mapping_status)
        else:
            aga_txt = "BETA • Aga Bekleniyor..."
        draw_text_fit(aga_txt, font_small, (140, 240, 255), aga_box.centerx, aga_box.centery, aga_box.width - 10)

    if active_dimension == "OVERWORLD" and warden_active and enemies:
        w_en = enemies[0]
        bar_y = int(HEIGHT * 0.132) if game_mode == "MULTI" else int(HEIGHT * 0.075)
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

    if active_dimension == "OVERWORLD" and end_portal_unlocked and end_portal_screen_rect.width > 0:
        label_y = max(12, end_portal_screen_rect.y - 10)
        draw_text_fit("END PORTALI • GİR", font_small, (225, 175, 255),
                      end_portal_screen_rect.centerx, label_y, int(WIDTH * 0.62))

    if has_gun:
        pygame.draw.rect(screen, (220, 145, 20), market_btn_rect, border_radius=10)
        pygame.draw.rect(screen, (255, 240, 150), market_btn_rect, 2, border_radius=10)
        draw_text_fit("MARKET [AÇ]", font_small, (255, 255, 255), market_btn_rect.centerx, market_btn_rect.centery, market_btn_rect.width - 10)

        if _adm_unlocked:
            pygame.draw.rect(screen, (150, 30, 200), admin_hud_btn_rect, border_radius=10)
            pygame.draw.rect(screen, (240, 180, 255), admin_hud_btn_rect, 2, border_radius=10)
            draw_text_fit("ADMİN [AÇ]", font_small, (255, 255, 255), admin_hud_btn_rect.centerx, admin_hud_btn_rect.centery, admin_hud_btn_rect.width - 10)

    if dialog_active and not market_open and not _adm_open and not nether_inventory_open:
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

    if game_mode != "MULTI" and active_dimension == "OVERWORLD" and not warden_active:
        _draw_vital_bars()
    draw_nether_hud()
    draw_update_controls()
    draw_market_admin_overlays()

    if damage_flash > 0 or (troll_state == "CHASE" and not _dede_eliminated):
        pygame.draw.rect(screen, (220, 20, 20), (0, 0, WIDTH, HEIGHT), 8)

    if _gl_render_lock_state:
        _warn_rect = pygame.Rect(int(WIDTH * 0.04), int(HEIGHT * 0.345), int(WIDTH * 0.92), int(HEIGHT * 0.10))
        _flash_on = (pygame.time.get_ticks() // 260) % 2 == 0
        _warn_bg = (130, 0, 0) if _flash_on else (55, 0, 0)
        pygame.draw.rect(screen, _warn_bg, _warn_rect, border_radius=10)
        pygame.draw.rect(screen, (255, 60, 60), _warn_rect, 3, border_radius=10)
        draw_text_fit("EKONOMİ DOĞRULAMASI", font_ui, (255, 255, 255), _warn_rect.centerx, _warn_rect.y + int(_warn_rect.height * 0.33), _warn_rect.width - 14)
        draw_text_fit(_economy_warning or "Satın alma ve ödüller durduruldu.", font_small, (255, 210, 210), _warn_rect.centerx, _warn_rect.y + int(_warn_rect.height * 0.72), _warn_rect.width - 14)

    pygame.display.flip()

_stop_network_session()
pygame.quit()
sys.exit()
