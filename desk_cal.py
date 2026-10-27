# -*- coding: utf-8 -*-
"""바탕화면 달력 — DesktopCal 대신 바탕화면에 붙는 월간 달력 + 노션 '긴영상 후보' 연동 (2026-10-26 사용자 요청).

칸 더블클릭 → 그 날짜의 후보 창. 위에 게임 버튼(노션 '게임' 값으로 자동, 하나 고름 — 토요일 기본 = 마크)과
단계 버튼(확정 = 촬영 확정·예정 / 후보 = 다음 순위·후보 / 검토 = 그 밖 전부, 여러 개 켬 — 기본 = 확정+후보)이 있고,
목록은 상태 순(촬영 확정 → 예정 → 다음 순위 → 후보 → 조사 대기 → 대기 → 보류) · 같은 상태면 배율 높은 순, 상태별 소제목.
업로드됨·제외·안 함☑·롱폼 업로드☑ 행은 안 띄운다. 하나 고르면 그 행의 '촬영일'에 날짜를 적고(노션이 원본)
칸은 게임 색으로 칠해지고 제목이 박힌다. 노션에서 촬영일을 직접 바꿔도 5분마다 다시 읽어 반영한다.
메모·칸 색은 이 PC에만 둔다(후보 창 아래 '메모'). 오른쪽 클릭 = 노션 새로고침·끝내기.

  pythonw desk_cal.py                    실행 (한 개만 뜬다)
  python desk_cal.py --at X,Y,W,H        위치·크기를 바꿔 저장하고 실행 (기본 = 처음 실행 때 DesktopCal 자리)
  python desk_cal.py --autostart on|off  로그인 때 자동 실행 등록/해제 (HKCU Run 'NabuDeskCal')

exe 배포판(10-27 조나스용, desk_cal_release.py가 GitHub 공개 저장소 릴리스로 낸다): 처음 실행하면
%LOCALAPPDATA%\\nabu-desk-cal\\desk_cal.exe로 복사·자동 실행 등록하고, 6시간마다 새 릴리스를 받아 스스로 바꿔 띄운다.
노션 토큰·후보 표는 ⚙ 설정의 '노션 연결'에 넣는다(config.json — 이 PC의 ~/.config/notion/.env보다 먼저).

데이터: %APPDATA%\\nabu-desk-cal\\ — cells.json(메모·색) holidays.json notion_cache.json config.json desk_cal.log
cells.json 이 없으면(첫 실행) DesktopCal DB(%APPDATA%\\CalendarTask\\Db\\calendar.db)의 칸·공휴일·최근 색을 읽기 전용으로 가져온다.
공휴일은 desk_cal_holidays.json(exe에 같이 묶임)이 먼저 — DesktopCal 없는 PC도 공휴일이 뜨게.
🔴 DesktopCal 색은 BGR hex(COLORREF) — 'f43737' = 파랑 #3737f4.
"""
import argparse
import collections
import colorsys
import ctypes
import ctypes.wintypes as W
import datetime as dt
import functools
import hashlib
import json
import math
import os
import queue
import re
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
import traceback
import urllib.error
import urllib.request
import zlib
from pathlib import Path
import tkinter as tk
import tkinter.font as tkfont
from tkinter import colorchooser, ttk

VERSION = "1.0.0"  # exe 배포판 — 올리고 desk_cal_release.py를 돌리면 설치된 exe들이 받아 간다
REPO = "abcaba123/nabu-desk-cal"
FROZEN = getattr(sys, "frozen", False)
INSTALL = Path(os.environ["LOCALAPPDATA"]) / "nabu-desk-cal" / "desk_cal.exe"
DATA = Path(os.environ["APPDATA"]) / "nabu-desk-cal"
DKCAL_DB = Path(os.environ["APPDATA"]) / "CalendarTask" / "Db" / "calendar.db"
ENV = Path.home() / ".config" / "notion" / ".env"
HOLIDAYS = Path(getattr(sys, "_MEIPASS", Path(__file__).parent)) / "desk_cal_holidays.json"
NV = "2022-06-28"
SYNC_MS = 5 * 60 * 1000
UPDATE_MS = 6 * 3600 * 1000
MUTEX = None

STATUS_ORDER = ["촬영 확정", "예정", "다음 순위", "후보", "조사 대기", "대기", "보류"]
HIDE_STATUS = {"업로드됨", "제외"}
# 후보 창 단계 버튼(10-27 사용자 「단계 3개로 묶기」) — 자동 수집 '대기' 행이 매일 늘어 기본은 확정+후보만
STAGES = [("확정", {"촬영 확정", "예정"}), ("후보", {"다음 순위", "후보"}), ("검토", None)]  # None = 나머지 전부(새 상태 포함)
GAME_ORDER = ["마크", "GTA", "공통"]
STATUS_BG = {"촬영 확정": "#2e7d32", "예정": "#00838f", "다음 순위": "#1565c0", "후보": "#546e7a",
             "조사 대기": "#6d4c41", "대기": "#616161", "보류": "#424242"}
GAME_BG = {"마크": "#3737f4", "GTA": "#c2185b", "공통": "#00897b"}  # 마크 = 사용자가 DesktopCal '마크 컨텐츠'에 쓴 파랑
# DesktopCal 테마에서 뽑은 색 (10-26 화면 캡처)
FRAME, HEAD, CELL, WEEKEND, TODAY, HOLI = "#4a5459", "#3a3b3c", "#3a3b3c", "#d34b09", "#ffd54f", "#ffd54f"
POP_BG, ROW_BG, ROW_HOVER = "#2f3133", "#3a3c3e", "#4a4d50"
FONT = "맑은 고딕"
DOW = "일월화수목금토"
# 달력 글꼴 [글꼴, 크기pt, 굵게, 색] — 첫 실행 때 DesktopCal 설정에서 가져와 config.json "fonts"에 둔다(⚙ 설정에서 바꿈)
DEFAULT_FONTS = {"date": [FONT, 10, True, "#ffffff"], "memo": [FONT, 10, False, "#ffffff"], "today": TODAY}
# 날짜 옆 작은 글씨(DesktopCal 24절기·기념일 표시 옮김, 10-27) — 공휴일은 holidays.json
TERM_COLOR = "#9ccc65"
TERMS = ["소한", "대한", "입춘", "우수", "경칩", "춘분", "청명", "곡우", "입하", "소만", "망종", "하지",
         "소서", "대서", "입추", "처서", "백로", "추분", "한로", "상강", "입동", "소설", "대설", "동지"]
MEMORIAL = {(2, 14): "발렌타인데이", (3, 14): "화이트데이", (4, 1): "만우절", (4, 5): "식목일", (5, 1): "근로자의 날",
            (5, 8): "어버이날", (5, 15): "스승의 날", (7, 17): "제헌절", (10, 1): "국군의 날", (10, 31): "할로윈",
            (11, 11): "빼빼로데이", (12, 24): "크리스마스 이브"}  # + 추수감사절(11월 넷째 목요일)
_TERMS_CACHE = {}
# 칸 색 고르기(10-27 사용자 「색깔이 너무 제한적 … 채도를 바꾸고 싶음 흰색 글씨에 맞는 색깔」) — 색상 16칸 × 밝게/진하게
SWATCH_HUES = [0, 15, 30, 45, 60, 90, 130, 160, 180, 200, 215, 240, 265, 290, 315, 340]
SWATCH_LUM = (0.183, 0.07)  # 흰 글씨 대비 4.5:1(웹 접근성 AA) / 약 8.8:1

u = ctypes.windll.user32
k32 = ctypes.WinDLL("kernel32", use_last_error=True)
ENUMPROC = ctypes.WINFUNCTYPE(W.BOOL, W.HWND, W.LPARAM)
u.FindWindowW.restype = W.HWND
u.FindWindowW.argtypes = [W.LPCWSTR, W.LPCWSTR]
u.FindWindowExW.restype = W.HWND
u.FindWindowExW.argtypes = [W.HWND, W.HWND, W.LPCWSTR, W.LPCWSTR]
u.SetParent.restype = W.HWND
u.SetParent.argtypes = [W.HWND, W.HWND]
u.GetParent.restype = W.HWND
u.GetParent.argtypes = [W.HWND]
u.IsWindow.argtypes = [W.HWND]
u.GetWindowLongPtrW.restype = ctypes.c_ssize_t
u.GetWindowLongPtrW.argtypes = [W.HWND, ctypes.c_int]
u.SetWindowLongPtrW.restype = ctypes.c_ssize_t
u.SetWindowLongPtrW.argtypes = [W.HWND, ctypes.c_int, ctypes.c_ssize_t]
u.SetWindowPos.argtypes = [W.HWND, W.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_uint]
u.ClientToScreen.argtypes = [W.HWND, ctypes.POINTER(W.POINT)]
u.GetWindowRect.argtypes = [W.HWND, ctypes.POINTER(W.RECT)]
u.GetClassNameW.argtypes = [W.HWND, W.LPWSTR, ctypes.c_int]
u.EnumChildWindows.argtypes = [W.HWND, ENUMPROC, W.LPARAM]
u.SetLayeredWindowAttributes.argtypes = [W.HWND, W.DWORD, ctypes.c_ubyte, W.DWORD]
u.MonitorFromPoint.restype = W.HMONITOR
u.MonitorFromPoint.argtypes = [W.POINT, W.DWORD]


def log(msg):
    DATA.mkdir(parents=True, exist_ok=True)
    with open(DATA / "desk_cal.log", "a", encoding="utf-8") as f:
        f.write(f"{dt.datetime.now():%m-%d %H:%M:%S} {msg}\n")


def jload(name, default):
    try:
        return json.loads((DATA / name).read_text(encoding="utf-8"))
    except FileNotFoundError:
        return default


def jsave(name, obj):
    DATA.mkdir(parents=True, exist_ok=True)
    tmp = DATA / (name + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, DATA / name)


def backup_cells():
    """하루 한 번 cells.json 사본(최근 30개) — 메모는 이 PC에만 있다"""
    src, bdir = DATA / "cells.json", DATA / "backup"
    if not src.exists():
        return
    bdir.mkdir(parents=True, exist_ok=True)
    dst = bdir / f"cells_{dt.date.today().isoformat()}.json"
    if not dst.exists():
        shutil.copyfile(src, dst)
    for old in sorted(bdir.glob("cells_*.json"))[:-30]:
        old.unlink()


def bmp(s):
    """Tk 8.6은 BMP 밖 글자(이모지 다수)를 못 그린다 — 빼고 그린다"""
    return "".join(c for c in (s or "") if ord(c) <= 0xFFFF)


def colorref(h):
    """DesktopCal 색(BGR hex) → #rrggbb. 빈 값·이상한 값은 None"""
    try:
        n = int(h, 16)
    except (TypeError, ValueError):
        return None
    return f"#{n & 0xFF:02x}{(n >> 8) & 0xFF:02x}{(n >> 16) & 0xFF:02x}"


# ───────────── 노션 ─────────────
_ENV = {}


def env():
    """노션 토큰·표 id — ⚙ '노션 연결'(config.json "notion")이 먼저, 없으면 ~/.config/notion/.env"""
    if not _ENV:
        if ENV.exists():
            for line in ENV.read_text(encoding="utf-8").splitlines():
                if "=" in line and not line.startswith("#"):
                    k, v = line.split("=", 1)
                    _ENV[k.strip()] = v.strip().strip('"')
        n = jload("config.json", {}).get("notion") or {}
        _ENV.update({k: v for k, v in (("NOTION_TOKEN", n.get("token")), ("NOTION_DB_LONG", n.get("db"))) if v})
    return _ENV


def notion(method, path, body=None):
    if not env().get("NOTION_TOKEN") or not env().get("NOTION_DB_LONG"):
        raise RuntimeError("⚙ 설정에서 노션 연결")
    req = urllib.request.Request(
        "https://api.notion.com/v1/" + path, method=method,
        data=None if body is None else json.dumps(body).encode(),
        headers={"Authorization": "Bearer " + env()["NOTION_TOKEN"], "Notion-Version": NV,
                 "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            return json.load(r)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f"HTTP {e.code} {e.read().decode(errors='replace')[:200]}") from None


def parse_row(p):
    pr = p["properties"]

    def get(name, kind):
        x = (pr.get(name) or {}).get(kind)
        if kind == "title":
            return "".join(t["plain_text"] for t in x or [])
        if kind == "select":
            return (x or {}).get("name")
        if kind == "date":
            return ((x or {}).get("start") or "")[:10] or None
        return x

    return {"id": p["id"], "title": get("제목", "title"), "game": get("게임", "select"),
            "status": get("상태", "select"), "ratio": get("배율", "number"), "shoot": get("촬영일", "date"),
            "skip": bool(get("안 함", "checkbox")), "uploaded": bool(get("롱폼 업로드", "checkbox"))}


def fetch_rows():
    db, rows, cur = env().get("NOTION_DB_LONG"), [], None  # 없으면 notion()이 '⚙ 설정에서 노션 연결'
    while True:
        res = notion("POST", f"databases/{db}/query", {"page_size": 100, **({"start_cursor": cur} if cur else {})})
        rows += [parse_row(p) for p in res["results"]]
        if not res.get("has_more"):
            return rows
        cur = res["next_cursor"]


def set_shoot(page_id, iso):
    notion("PATCH", f"pages/{page_id}", {"properties": {"촬영일": {"date": {"start": iso} if iso else None}}})


def stage_of(status):
    return next(name for name, members in STAGES if members is None or status in members)


def candidates(rows, day):
    """그날 후보 창에 올릴 수 있는 행(게임·단계 거르기는 창의 버튼이 한다). 이미 그날 배정된 행은 뺀다"""
    iso = day.isoformat()
    out = [r for r in rows if r["status"] not in HIDE_STATUS and not r["skip"] and not r["uploaded"]
           and r["shoot"] != iso]
    rank = {s: i for i, s in enumerate(STATUS_ORDER)}
    return sorted(out, key=lambda r: (rank.get(r["status"], len(STATUS_ORDER)), -(r["ratio"] or 0)))


# ───────────── DesktopCal 가져오기 ─────────────
def import_desktopcal():
    cells, holidays, palette = {}, {}, []
    if not DKCAL_DB.exists():
        return cells, holidays, palette
    con = sqlite3.connect(DKCAL_DB.as_uri() + "?mode=ro", uri=True)
    try:
        for uid, bg, text in con.execute(
                "select it_unique_id, it_bgcolor, it_content from item_table where it_unique_id like 'dkcal_mdays_%'"):
            d = uid.rsplit("_", 1)[1]
            if len(d) != 8 or not d.isdigit():
                continue
            text = (text or "").replace("\r\n", "\n").strip()
            rgb = colorref(bg)
            if text or rgb:
                cells[f"{d[:4]}-{d[4:6]}-{d[6:]}"] = {"text": text, "bg": rgb}
        row = con.execute("select st_sval from setting_table where st_name='sys_setting_holidayv2_local_kr_ko'").fetchone()
        if row:
            try:
                v = json.loads(row[0].replace("|&quot;|", '"').replace("&quot;", '"'))
                for h in v["vdata"]["kr_ko"]["data"]:
                    holidays[h["day"]] = " · ".join(h["title"])
            except (ValueError, KeyError, TypeError) as e:
                log(f"공휴일 못 읽음: {e}")
        row = con.execute("select st_sval from setting_table where st_name='sys_recent_bkgnd_color'").fetchone()
        if row:
            palette = [colorref(format(int(n), "x")) for n in row[0].split(",") if n.strip().isdigit()]
    finally:
        con.close()
    return cells, holidays, palette


def luminance(hexc):
    """WCAG 상대 휘도 — 흰 글씨 대비 = 1.05 / (휘도 + 0.05)"""
    def ch(v):
        v /= 255
        return v / 12.92 if v <= 0.03928 else ((v + 0.055) / 1.055) ** 2.4
    r, g, b = (int(hexc[i:i + 2], 16) for i in (1, 3, 5))
    return 0.2126 * ch(r) + 0.7152 * ch(g) + 0.0722 * ch(b)


@functools.lru_cache(maxsize=512)
def white_text_colors(sat, max_lum):
    """색상마다 흰 글씨가 읽히는(휘도 ≤ max_lum) 가장 밝은 색. sat = 채도 0~1"""
    out = []
    for h in SWATCH_HUES:
        lo, hi = 0.0, 1.0
        for _ in range(18):
            mid = (lo + hi) / 2
            r, g, b = colorsys.hls_to_rgb(h / 360, mid, sat)
            if luminance(f"#{round(r * 255):02x}{round(g * 255):02x}{round(b * 255):02x}") <= max_lum:
                lo = mid
            else:
                hi = mid
        r, g, b = colorsys.hls_to_rgb(h / 360, lo, sat)
        out.append(f"#{round(r * 255):02x}{round(g * 255):02x}{round(b * 255):02x}")
    return out


def sun_lon(jd):
    """태양 겉보기 황경(도) — Meeus 저정밀식(약 0.01°, 시각으로 15분 안팎)"""
    T = (jd - 2451545.0) / 36525
    L0 = 280.46646 + 36000.76983 * T + 0.0003032 * T * T
    M = math.radians(357.52911 + 35999.05029 * T - 0.0001537 * T * T)
    C = ((1.914602 - 0.004817 * T - 0.000014 * T * T) * math.sin(M) + (0.019993 - 0.000101 * T) * math.sin(2 * M)
         + 0.000289 * math.sin(3 * M))
    return (L0 + C - 0.00569 - 0.00478 * math.sin(math.radians(125.04 - 1934.136 * T))) % 360


def solar_terms(year):
    """{'YYYY-MM-DD': 절기} 한국 시간 날짜. 2026 입동 11/7·소설 11/22(DesktopCal 화면)과 맞춤"""
    if year not in _TERMS_CACHE:
        out, jd0 = {}, 2451544.5 + (dt.date(year, 1, 6) - dt.date(2000, 1, 1)).days
        for k, name in enumerate(TERMS):
            target, jd = (285 + 15 * k) % 360, jd0 + 15.2 * k
            for _ in range(8):
                jd += ((target - sun_lon(jd) + 180) % 360 - 180) / 0.98565
            out[(dt.datetime(2000, 1, 1, 21) + dt.timedelta(days=jd - 2451545.0)).date().isoformat()] = name  # +9h
        _TERMS_CACHE[year] = out
    return _TERMS_CACHE[year]


def import_fonts():
    """DesktopCal 글꼴 설정(날짜 숫자 board_calendar_font·칸 글씨 board_item_font) → DEFAULT_FONTS 꼴"""
    out = {}
    if not DKCAL_DB.exists():
        return out
    con = sqlite3.connect(DKCAL_DB.as_uri() + "?mode=ro", uri=True)
    try:
        for key, name in (("date", "board_calendar_font"), ("memo", "board_item_font")):
            row = con.execute("select st_sval from setting_table where st_name=?", (name,)).fetchone()
            try:
                j = json.loads(row[0].replace("|&quot;|", '"').replace("&quot;", '"'))
                lf = j["lpLogFont"]
                out[key] = [lf["lfFaceName"], round(abs(lf["lfHeight"]) * 72 / (j.get("deviceCapsY") or 96)),
                            lf["lfWeight"] >= 600, colorref(format(int(j["rgbColors"]), "x"))]
            except (TypeError, ValueError, KeyError) as e:
                log(f"DesktopCal 글꼴 {name} 못 읽음: {e}")
    finally:
        con.close()
    return out


# ───────────── 바탕화면에 붙이기 (DesktopCal과 같은 방식: 아이콘 목록 창의 자식) ─────────────
def desktop_listview():
    def in_(parent):
        dv = u.FindWindowExW(parent, None, "SHELLDLL_DefView", None)
        return u.FindWindowExW(dv, None, "SysListView32", None) if dv else None

    lv = in_(u.FindWindowW("Progman", None))
    w = None
    while not lv:  # 배경 슬라이드쇼 등으로 DefView가 WorkerW 밑에 있을 때
        w = u.FindWindowExW(None, w, "WorkerW", None)
        if not w:
            return None
        lv = in_(w)
    return lv


def dkcal_rect(lv):
    found = []

    def cb(h, _):
        cls = ctypes.create_unicode_buffer(64)
        u.GetClassNameW(h, cls, 64)
        r = W.RECT()
        u.GetWindowRect(h, ctypes.byref(r))
        if cls.value == "xUIWindow" and r.right - r.left > 400:
            found.append((r.left, r.top, r.right - r.left, r.bottom - r.top))
        return True

    u.EnumChildWindows(lv, ENUMPROC(cb), 0)
    return found[0] if found else None


def attach(hwnd, lv, rect):
    GWL_STYLE, WS_CHILD, WS_POPUP = -16, 0x40000000, 0x80000000
    st = u.GetWindowLongPtrW(hwnd, GWL_STYLE) & 0xFFFFFFFF
    u.SetWindowLongPtrW(hwnd, GWL_STYLE, (st & ~WS_POPUP) | WS_CHILD)
    if not u.SetParent(hwnd, lv):
        return False
    pt = W.POINT(0, 0)
    u.ClientToScreen(lv, ctypes.byref(pt))
    x, y, w, h = rect
    u.SetWindowPos(hwnd, None, x - pt.x, y - pt.y, w, h, 0x0020 | 0x0040 | 0x0010)  # FRAMECHANGED|SHOWWINDOW|NOACTIVATE
    return True


def work_area(x, y):
    class MI(ctypes.Structure):
        _fields_ = [("cbSize", W.DWORD), ("rcMonitor", W.RECT), ("rcWork", W.RECT), ("dwFlags", W.DWORD)]

    mi = MI()
    mi.cbSize = ctypes.sizeof(MI)
    u.GetMonitorInfoW(u.MonitorFromPoint(W.POINT(x, y), 2), ctypes.byref(mi))
    r = mi.rcWork
    return r.left, r.top, r.right, r.bottom


def default_rect():
    """DesktopCal 창이 없는 PC의 첫 자리 — 주 모니터 작업 영역 오른쪽 60%"""
    left, top, right, bottom = work_area(0, 0)
    w = int((right - left) * 0.6)
    return right - w - 7, top + 7, w, bottom - top - 14


# ───────────── exe 배포판: 설치·자동 업데이트 ─────────────
def ver(s):
    return tuple(int(x) for x in re.findall(r"\d+", s))


def fetch_update():
    """GitHub 최신 릴리스가 더 새 버전이면 desk_cal.new.exe로 받고 크기·sha256(릴리스 본문)을 맞춰 본다. 아니면 None"""
    def get(url):
        return urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "nabu-desk-cal"}), timeout=60)

    try:
        with get(f"https://api.github.com/repos/{REPO}/releases/latest") as r:
            rel = json.load(r)
        if ver(rel["tag_name"]) <= ver(VERSION):
            return None
        asset = next(a for a in rel["assets"] if a["name"] == "desk_cal.exe")
        want = re.search(r"sha256:\s*([0-9a-f]{64})", rel.get("body") or "").group(1)
        new, h = INSTALL.with_name("desk_cal.new.exe"), hashlib.sha256()
        with get(asset["browser_download_url"]) as r, open(new, "wb") as f:
            while chunk := r.read(1 << 16):
                h.update(chunk)
                f.write(chunk)
        if h.hexdigest() != want or new.stat().st_size != asset["size"]:
            new.unlink()
            log(f"업데이트 {rel['tag_name']} 파일 확인 실패 — 버림")
            return None
        log(f"업데이트 {rel['tag_name']} 받음")
        return new
    except Exception as e:
        log(f"업데이트 확인 실패: {e}")
        return None


def relaunch():
    """설치본을 새로 띄운다 — 한 파일 exe가 자기를 띄울 땐 압축 풀린 폴더를 물려받지 않게(PyInstaller 6.9+)"""
    subprocess.Popen([str(INSTALL)], env={**os.environ, "PYINSTALLER_RESET_ENVIRONMENT": "1"},
                     creationflags=0x00000008 | 0x00000200)  # DETACHED_PROCESS | CREATE_NEW_PROCESS_GROUP


def install():
    """다운로드 폴더 등에서 처음 실행 → 설치 자리로 복사·자동 실행 등록 후 설치본을 띄운다(업데이트가 늘 같은 파일을 바꾸게)"""
    INSTALL.parent.mkdir(parents=True, exist_ok=True)
    try:
        shutil.copyfile(sys.executable, INSTALL)
    except OSError:  # 설치본이 켜져 있어 못 덮음
        u.MessageBoxW(None, "달력이 이미 켜져 있어요.", "바탕화면 달력", 0x40)
        return
    set_autostart(True)
    relaunch()


# ───────────── 달력 ─────────────
class DeskCal:
    def __init__(self, cfg, attach_desktop=True):
        self.cfg, self.rect, self.palette = cfg, tuple(cfg["rect"]), cfg.get("palette", [])
        rect = self.rect
        self.month = dt.date.today().replace(day=1)
        self.cells = jload("cells.json", {})
        try:
            bundled = json.loads(HOLIDAYS.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            bundled = {}
        self.holidays = {**jload("holidays.json", {}), **bundled}
        self.relaunch, self.update_file = False, None
        cache = jload("notion_cache.json", {})
        self.rows, self.synced, self.err = cache.get("rows", []), cache.get("at"), None
        self.q, self.popup, self.quit, self.syncing = queue.Queue(), None, False, False
        self.local = {}  # 행 id → (촬영일, 저장 끝난 시각) — 저장 전에 출발한 읽기가 늦게 와도 덮지 않게
        self.want_attach = attach_desktop
        self.saving, self.rows_started = False, 0.0
        self.today_seen = dt.date.today()
        self.stages = {"확정", "후보"}  # 후보 창 단계 버튼 — 달력이 켜져 있는 동안 기억
        self.root = tk.Tk()
        try:
            self._build(rect, attach_desktop)
        except Exception:
            self.root.destroy()  # 반쯤 만든 창을 남기면 다시 만들 때 두 개가 된다(Codex desk-cal-rebut 6)
            raise

    def _build(self, rect, attach_desktop):
        self.root.overrideredirect(True)
        self.root.report_callback_exception = lambda *a: log("".join(traceback.format_exception(*a)))
        x, y, w, h = rect
        self.root.geometry(f"{w}x{h}+{x}+{y}")
        self.cv = tk.Canvas(self.root, bg=FRAME, highlightthickness=0, width=w, height=h)
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Button-1>", self.on_click)
        self.cv.bind("<Double-Button-1>", self.on_double)
        self.cv.bind("<Button-3>", self.on_menu)
        self.cv.bind("<MouseWheel>", lambda e: self.shift(-1 if e.delta > 0 else 1))
        self.root.update()
        self.hwnd = int(self.root.wm_frame(), 16)
        self.lv = desktop_listview() if attach_desktop else None
        if self.lv and not attach(self.hwnd, self.lv, rect):
            self.lv = None  # 못 붙었으면 watch()가 5초마다 다시 시도
        if attach_desktop and not self.lv:
            log("바탕화면에 못 붙음 — 일반 창으로 뜨고 5초마다 다시 시도")
        self.apply_alpha()
        self.draw()
        self.sync()
        self.root.after(200, self.pump)
        self.root.after(SYNC_MS, self.tick)
        self.root.after(5000, self.watch)
        if FROZEN:
            self.root.after(30_000, self.check_update)

    def check_update(self):
        self.root.after(UPDATE_MS, self.check_update)
        threading.Thread(target=lambda: self.q.put(("update", fetch_update())), daemon=True).start()

    def try_update(self):
        """받아 둔 새 exe로 바꿔 띄운다 — 후보 창·설정 창을 쓰는 중이면 1분 뒤 다시. 실행 중인 exe는 지울 순 없어도 이름은 바꿀 수 있다"""
        if self.popup or (getattr(self, "settings", None) and self.settings.top.winfo_exists()):
            self.root.after(60_000, self.try_update)
            return
        old = INSTALL.with_name("desk_cal.old.exe")
        try:
            os.replace(INSTALL, old)
            os.replace(self.update_file, INSTALL)
        except OSError as e:
            log(f"업데이트 못 바꿈: {e}")
            if not INSTALL.exists() and old.exists():
                os.replace(old, INSTALL)
            return
        log("업데이트 — 새 exe로 다시 띄움")
        self.relaunch = True
        self.stop()

    # 노션 동기화 — 네트워크는 스레드에서, Tk는 이 스레드에서만 만진다
    def sync(self):
        if self.syncing:
            return
        self.syncing = True
        started = time.monotonic()

        def work():
            try:
                self.q.put(("rows", fetch_rows(), started))
            except Exception as e:
                self.q.put(("err", f"노션 못 읽음: {e}"))

        threading.Thread(target=work, daemon=True).start()

    def assign(self, row, iso):
        if self.saving:  # 저장 하나가 끝나기 전 클릭은 무시
            return
        self.saving = True
        if self.popup:
            self.popup.set_status("노션에 저장 중…", "#b0bec5")

        def work():
            try:
                set_shoot(row["id"], iso)
                self.q.put(("assigned", row["id"], iso, time.monotonic()))
            except Exception as e:
                self.q.put(("assign_err", f"노션에 못 씀: {e}"))

        threading.Thread(target=work, daemon=True).start()

    def pump(self):
        try:
            while True:
                msg = self.q.get_nowait()
                if msg[0] == "rows":
                    rows, started = msg[1], msg[2]
                    self.syncing = False
                    if started < self.rows_started:  # 더 늦게 출발한 읽기가 이미 반영됨
                        continue
                    self.rows_started = started
                    self.local = {k: v for k, v in self.local.items() if v[1] > started}
                    for r in rows:
                        if r["id"] in self.local:
                            r["shoot"] = self.local[r["id"]][0]
                    same = rows == self.rows and self.err is None
                    self.err = None
                    self.rows, self.synced = rows, dt.datetime.now().isoformat(timespec="minutes")
                    jsave("notion_cache.json", {"at": self.synced, "rows": self.rows})
                    if same:  # 바뀐 게 없으면 시각만 — 다 다시 그리면 후보 목록이 맨 위로 튀고 채도 막대가 끊긴다
                        self.refresh_status()
                        continue
                elif msg[0] == "assigned":
                    self.saving = False
                    self.local[msg[1]] = (msg[2], msg[3])
                    for r in self.rows:
                        if r["id"] == msg[1]:
                            r["shoot"] = msg[2]
                    jsave("notion_cache.json", {"at": self.synced, "rows": self.rows})
                    if msg[2] and self.popup:  # 골랐으면 창 닫기, 뺐으면 창 그대로
                        self.popup.close()
                elif msg[0] == "assign_err":  # 읽기 상태(syncing·err)는 건드리지 않는다
                    self.saving = False
                    log(msg[1])
                    if self.popup:
                        self.popup.set_status(msg[1], "#ff8a80")
                    continue
                elif msg[0] == "update":
                    if msg[1]:
                        self.update_file = msg[1]
                        self.root.after(0, self.try_update)  # pump 밖에서 — 창을 닫은 뒤 pump가 다음 예약을 못 건다
                    continue
                elif msg[0] == "err":
                    self.syncing, self.err = False, msg[1]
                    log(msg[1])
                self.draw()
                if self.popup:
                    self.popup.render()
        except queue.Empty:
            pass
        except Exception:  # 파일 쓰기 실패 등 — 예약이 끊기면 그 뒤 노션 결과를 영영 못 받는다(Codex desk-cal-gap 8)
            log("pump 오류\n" + traceback.format_exc())
        finally:
            self.root.after(200, self.pump)

    def tick(self):
        self.sync()
        self.root.after(SYNC_MS, self.tick)

    def watch(self):
        """탐색기가 다시 뜨면 아이콘 창이 바뀐다. 우리 창이 같이 죽었으면 바깥 루프가 다시 만들고,
        살아 있는데 붙을 곳이 없으면(탐색기가 늦게 뜸) 새 아이콘 창을 찾아 다시 붙는다"""
        if not u.IsWindow(self.hwnd):
            log("바탕화면 창과 같이 닫힘 — 다시 만든다")
            self.stop(restart=True)
            return
        self.root.after(5000, self.watch)  # 먼저 예약 — 아래에서 오류가 나도 감시가 안 끊긴다(Codex desk-cal-gap 5)
        try:
            if self.want_attach and (not self.lv or not u.IsWindow(self.lv)):
                lv = desktop_listview()
                if lv and attach(self.hwnd, lv, self.rect):
                    self.lv = lv
                    self.apply_alpha()
                    log("바탕화면에 다시 붙음")
            today = dt.date.today()
            if today != self.today_seen:  # 자정 지남 — 보던 달이 그때의 '오늘 달'이면 새 달로, 오늘 테두리도 옮긴다
                if self.month == self.today_seen.replace(day=1):
                    self.month = today.replace(day=1)
                self.today_seen = today
                self.draw()
                backup_cells()
        except Exception:
            log("watch 오류\n" + traceback.format_exc())

    def status_text(self):
        when = (self.synced or "")[5:].replace("T", " ").replace("-", "/")
        if self.err:
            return f"{self.err} — {when or '저장본 없음'} 저장본으로 보여 줌", "#ff8a80"
        return (f"노션 {when} 기준" if when else "노션 불러오는 중…"), "#b0bec5"

    def refresh_status(self):
        st, color = self.status_text()
        self.cv.itemconfig(self.status_item, text=bmp(st)[:40], fill=color)
        if self.popup:
            self.popup.set_status(st, color)

    def picks(self):
        out = {}
        for r in self.rows:
            if r["shoot"]:
                out.setdefault(r["shoot"], []).append(r)
        return out

    # 그리기
    def draw(self):
        cv, (_, _, w, h) = self.cv, self.rect
        cv.delete("all")
        self.hits, self.cellmap = [], []
        HH, M, G, DH = 40, 6, 2, 22
        cv.create_rectangle(0, 0, w, HH, fill=HEAD, width=0)
        t = cv.create_text(w // 2, HH // 2, text=f"{self.month.year}년{self.month.month}월 ▾", fill="#fff3c4",
                           font=(FONT, 12, "bold"))
        x1, _, x2, _ = cv.bbox(t)
        self.hits.append((x1 - 10, 0, x2 + 10, HH, self.open_month_picker))  # 누르면 연·월 바로 가기
        st, color = self.status_text()
        self.status_item = cv.create_text(M + 4, HH // 2, text=bmp(st)[:40], fill=color, anchor="w", font=(FONT, 9))
        bx = w - M
        for label, fn in [("⚙", self.open_settings), ("⟳", self.sync), ("›", lambda: self.shift(1)), ("오늘", self.today),
                          ("‹", lambda: self.shift(-1))]:
            t = cv.create_text(bx, HH // 2, text=label, fill="#ffffff", anchor="e", font=(FONT, 13 if len(label) == 1 else 10, "bold"))
            x1, y1, x2, y2 = cv.bbox(t)
            self.hits.append((x1 - 6, 0, x2 + 6, HH, fn))
            bx = x1 - 16
        cw = (w - 2 * M - 6 * G) / 7
        top = HH + 4
        for i, d in enumerate(DOW):
            x = M + i * (cw + G)
            cv.create_rectangle(x, top, x + cw, top + DH, fill=HEAD, width=0)
            cv.create_text(x + cw / 2, top + DH / 2, text=d + "요일", fill="#fff3c4", font=(FONT, 9))
        first = self.month
        off = (first.weekday() + 1) % 7  # 일요일 시작(DesktopCal과 같게)
        ndays = ((first.replace(day=28) + dt.timedelta(days=4)).replace(day=1) - first).days
        weeks = (off + ndays + 6) // 7
        gtop = top + DH + G
        ch = (h - gtop - M - (weeks - 1) * G) / weeks
        today, picks, fonts = dt.date.today(), self.picks(), self.fonts()
        fam, size, bold, dcol = fonts["date"]
        dfont = (fam, size, "bold" if bold else "normal")
        fam, size, bold, mcol = fonts["memo"]
        mfont, pfont = (fam, size, "bold" if bold else "normal"), (fam, size, "bold")  # pfont = 배정 제목·…
        for i in range(weeks * 7):
            day = first + dt.timedelta(days=i - off)
            if day.month != first.month:
                continue
            iso = day.isoformat()
            x = M + (i % 7) * (cw + G)
            y = gtop + (i // 7) * (ch + G)
            mine, cell = picks.get(iso, []), self.cells.get(iso, {})
            bg = (GAME_BG.get(mine[0]["game"], GAME_BG["마크"]) if mine else cell.get("bg")
                  or (WEEKEND if day.weekday() >= 5 else CELL))
            cv.create_rectangle(x, y, x + cw, y + ch, fill=bg, width=2 if day == today else 0,
                                outline=fonts["today"] if day == today else "")
            num = cv.create_text(x + 4, y + 3, text=str(day.day), fill=dcol, anchor="nw", font=dfont)
            ty = cv.bbox(num)[3] + 2
            lx = cv.bbox(num)[2] + 8
            for text, color in self.day_labels(day):
                lab = cv.create_text(lx, y + 4, text=text, fill=color, anchor="nw", font=(FONT, 9))
                lx = cv.bbox(lab)[2] + 6
            lines = [("▶ " + bmp(r["title"]), pfont) for r in mine]
            lines += [(bmp(t), mfont) for t in cell.get("text", "").split("\n") if t.strip()]
            for text, font in lines:
                t = cv.create_text(x + 4, ty, text=text, fill=mcol, anchor="nw", font=font, width=cw - 8)
                y2 = cv.bbox(t)[3]
                if y2 > y + ch - 2:
                    cv.delete(t)
                    cv.create_text(x + cw - 4, y + ch - 2, text="…", fill=mcol, anchor="se", font=pfont)
                    break
                ty = y2 + 1
            self.cellmap.append((x, y, x + cw, y + ch, day))

    def shift(self, n):
        m = self.month.month - 1 + n
        self.month = dt.date(self.month.year + m // 12, m % 12 + 1, 1)
        self.draw()

    def today(self):
        self.month = dt.date.today().replace(day=1)
        self.draw()

    def on_click(self, e):
        for x1, y1, x2, y2, fn in self.hits:
            if x1 <= e.x <= x2 and y1 <= e.y <= y2:
                fn()
                return

    def on_double(self, e):
        for x1, y1, x2, y2, day in self.cellmap:
            if x1 <= e.x <= x2 and y1 <= e.y <= y2:
                self.open_popup(day, e.x_root, e.y_root)
                return

    def open_popup(self, day, x, y):
        if self.popup:
            self.popup.close()
        self.popup = Popup(self, day, x, y)
        self.sync()

    def on_menu(self, e):
        m = tk.Menu(self.root, tearoff=0)
        m.add_command(label="노션 새로고침", command=self.sync)
        m.add_command(label="설정…", command=self.open_settings)
        m.add_separator()
        m.add_command(label="달력 끝내기", command=self.stop)
        m.tk_popup(e.x_root, e.y_root)

    def fonts(self):
        return {**DEFAULT_FONTS, **self.cfg.get("fonts", {})}

    def day_labels(self, day):
        """날짜 옆 작은 글씨: 공휴일 · 기념일 · 24절기(⚙에서 끄고 켬)"""
        iso, out = day.isoformat(), []
        hol = self.holidays.get(iso, "")
        if hol:
            out.append((bmp(hol), HOLI))
        if self.cfg.get("show_days", True):
            name = MEMORIAL.get((day.month, day.day))
            if day.month == 11 and day.weekday() == 3 and 22 <= day.day <= 28:
                name = "추수감사절"
            if name and name not in hol:
                out.append((name, HOLI))
        if self.cfg.get("show_terms", True) and iso in solar_terms(day.year):
            out.append((solar_terms(day.year)[iso], TERM_COLOR))
        return out

    def apply_alpha(self):
        """칸 투명도(⚙, 0~60%) — 창 전체에 걸려 글씨도 같이 옅어진다. 0이면 투명 끔"""
        pct = int(self.cfg.get("alpha", 0))
        ex = u.GetWindowLongPtrW(self.hwnd, -20)
        if pct > 0:
            u.SetWindowLongPtrW(self.hwnd, -20, ex | 0x80000)  # WS_EX_LAYERED
            u.SetLayeredWindowAttributes(self.hwnd, 0, round(255 * (100 - pct) / 100), 2)  # LWA_ALPHA
        elif ex & 0x80000:
            u.SetWindowLongPtrW(self.hwnd, -20, ex & ~0x80000)

    def open_settings(self):
        if getattr(self, "settings", None) and self.settings.top.winfo_exists():
            self.settings.top.lift()
            return
        self.settings = Settings(self)

    def open_month_picker(self):
        if getattr(self, "picker", None) and self.picker.top.winfo_exists():
            self.picker.top.destroy()  # 제목을 다시 누르면 닫힘
            return
        self.picker = MonthPicker(self, self.rect[0] + self.rect[2] // 2 - 125, self.rect[1] + 40)

    def stop(self, restart=False):
        """끝낼 때도 후보 창의 메모를 먼저 저장한다(Codex desk-cal-gap 6)"""
        if self.popup:
            self.popup.close()
        self.quit = not restart
        self.root.destroy()

    def save_cell(self, iso, text, bg):
        if text.strip() or bg:
            self.cells[iso] = {"text": text.strip(), "bg": bg}
        else:
            self.cells.pop(iso, None)
        jsave("cells.json", self.cells)
        self.draw()

    # 색 고르기 첫 줄(10-27 사용자 「최근에 사용하거나 자주 사용하는 색이 저장되면 좋겠는데」)
    def recent_colors(self):
        """최근 칠한 색 5개(최신 먼저, config recent_colors). 처음엔 DesktopCal의 최근 색"""
        return (self.cfg.get("recent_colors") or [c for c in self.palette[:4] if c])[:5]

    def note_color(self, c):
        rec = [c] + [x for x in self.recent_colors() if x != c]
        self.cfg["recent_colors"] = rec[:5]
        jsave("config.json", self.cfg)

    def frequent_colors(self, exclude, n=5):
        """달력 전체 칸에서 많이 쓴 색 n개(최근 줄과 겹치는 건 뺌) — 칠할 때마다 cells.json에서 다시 센다"""
        count = collections.Counter(v["bg"] for v in self.cells.values() if v.get("bg"))
        return [c for c, _ in count.most_common() if c not in exclude][:n]


class Popup:
    """칸 더블클릭 창: 그날 배정 · 후보 목록 · 메모/칸 색"""

    def __init__(self, app, day, x, y):
        self.app, self.day, self.iso = app, day, day.isoformat()
        t = self.top = tk.Toplevel(app.root)
        t.title(f"{day.month}월 {day.day}일 콘텐츠")
        t.configure(bg=POP_BG)
        t.attributes("-topmost", True)
        pw, ph, FR = 520, 660, 50  # FR = 제목 표시줄·테두리(geometry 높이에 안 들어감 — 10-26 작업 표시줄에 가림)
        l, tp, r, b = work_area(x, y)
        ph = min(ph, b - tp - FR)
        px = x + 12 if x + 12 + pw <= r else max(l, x - 12 - pw)
        py = min(max(tp, y - 40), max(tp, b - ph - FR))
        t.geometry(f"{pw}x{ph}+{px}+{py}")
        t.protocol("WM_DELETE_WINDOW", self.close)
        t.bind("<Escape>", lambda e: self.close())

        head = tk.Frame(t, bg=HEAD)
        head.pack(fill="x")
        tk.Label(head, text=f"{day.month}월 {day.day}일 ({DOW[(day.weekday() + 1) % 7]})", font=(FONT, 13, "bold"),
                 fg="#fff3c4", bg=HEAD).pack(side="left", padx=10, pady=8)
        self.status = tk.Label(t, anchor="w", bg=POP_BG, font=(FONT, 9), justify="left", wraplength=pw - 20)
        self.status.pack(fill="x", padx=10, pady=(4, 0))
        self.assigned = tk.Frame(t, bg=POP_BG)
        self.assigned.pack(fill="x")
        self.game = "마크" if day.weekday() == 5 else "전체"  # 10-26 사용자 '토=마크' — 기본값일 뿐, 버튼으로 바꾼다
        self.filters = tk.Frame(t, bg=POP_BG)
        self.filters.pack(fill="x")

        # 메모를 먼저 아래에 붙여야 목록이 남는 높이를 다 쓴다
        memo = tk.Frame(t, bg=POP_BG)
        memo.pack(side="bottom", fill="x", padx=10, pady=(4, 10))
        tk.Label(memo, text="메모 · 칸 색 (자동 저장, 이 PC에만)", fg="#b0bec5", bg=POP_BG, font=(FONT, 9)).pack(anchor="w")
        cell = app.cells.get(self.iso, {})
        self.orig = (cell.get("text", ""), cell.get("bg"))
        self.text = tk.Text(memo, height=3, font=(FONT, 10), bg="#232425", fg="#ffffff", insertbackground="#ffffff",
                            relief="flat", wrap="word")
        self.text.insert("1.0", cell.get("text", ""))
        self.text.pack(fill="x", pady=(2, 4))
        self.text.bind("<Control-Return>", lambda e: (self.save(), "break")[1])
        self._pending = None
        self.text.bind("<KeyRelease>", lambda e: self.schedule())  # 치는 중에도 1초 뒤 저장 — 로그오프·강제 종료 대비
        sw = tk.Frame(memo, bg=POP_BG)
        sw.pack(fill="x")
        self.bg, self.swatches, self.gen_swatches = cell.get("bg"), [], []
        self.swatch(sw, None, self.swatches, "없음")
        recent = app.recent_colors()
        for label, colors in (("최근", recent), ("자주", app.frequent_colors(exclude=recent))):
            if colors:
                tk.Label(sw, text=label, fg="#78909c", bg=POP_BG, font=(FONT, 8)).pack(side="left", padx=(6, 0))
                for c in colors:
                    self.swatch(sw, c, self.swatches)
        more = tk.Label(sw, text="직접…", fg="#ffffff", bg=ROW_BG, font=(FONT, 8), padx=6, cursor="hand2")
        more.bind("<Button-1>", lambda e: self.custom())
        more.pack(side="left", padx=4, ipady=2)
        tk.Button(sw, text="닫기", command=self.save, font=(FONT, 9), bg="#455a64", fg="#ffffff",
                  activebackground="#546e7a", relief="flat", padx=10).pack(side="right")
        self.gen = tk.Frame(memo, bg=POP_BG)
        self.gen.pack(fill="x", pady=(4, 0))
        satrow = tk.Frame(memo, bg=POP_BG)
        satrow.pack(fill="x")
        tk.Label(satrow, text="채도", fg="#b0bec5", bg=POP_BG, font=(FONT, 9)).pack(side="left")
        self.sat = tk.IntVar(value=int(app.cfg.get("swatch_sat", 80)))
        bar = tk.Scale(satrow, from_=20, to=100, orient="horizontal", variable=self.sat, showvalue=False, length=180,
                       command=lambda v: self.render_swatches(), bg=POP_BG, highlightthickness=0, troughcolor=ROW_BG)
        bar.bind("<ButtonRelease-1>", lambda e: self.save_sat())  # 파일은 손 뗄 때 한 번만
        bar.pack(side="left", padx=6)
        tk.Label(satrow, text="흰 글씨가 읽히는 색만 (대비 4.5:1 이상)", fg="#78909c", bg=POP_BG,
                 font=(FONT, 8)).pack(side="left")
        self.render_swatches()
        self.choose(self.bg)

        wrap = tk.Frame(t, bg=POP_BG)
        wrap.pack(fill="both", expand=True, padx=10, pady=(6, 0))
        self.cv = tk.Canvas(wrap, bg=POP_BG, highlightthickness=0)
        sb = tk.Scrollbar(wrap, command=self.cv.yview)
        self.cv.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.cv.pack(side="left", fill="both", expand=True)
        self.inner = tk.Frame(self.cv, bg=POP_BG)
        self.win = self.cv.create_window(0, 0, window=self.inner, anchor="nw")
        self.inner.bind("<Configure>", lambda e: self.cv.configure(scrollregion=self.cv.bbox("all")))
        self.cv.bind("<Configure>", lambda e: self.cv.itemconfigure(self.win, width=e.width))
        t.bind("<MouseWheel>", lambda e: self.cv.yview_scroll(-e.delta // 120, "units"))
        self.render()
        t.focus_force()

    def set_status(self, text, color):
        self.status.config(text=bmp(text), fg=color)

    def render(self):
        if not self.top.winfo_exists():
            return
        self.set_status(*self.app.status_text())
        for f in (self.assigned, self.filters, self.inner):
            for w in f.winfo_children():
                w.destroy()
        mine = [r for r in self.app.rows if r["shoot"] == self.iso]
        self.assigned.configure(height=1)  # 자식을 다 지워도 Tk 프레임은 옛 높이를 유지한다 — [빼기] 뒤 빈칸
        if mine:
            tk.Label(self.assigned, text="이 날 촬영", fg="#b0bec5", bg=POP_BG, font=(FONT, 9)).pack(anchor="w", padx=10, pady=(6, 0))
        for r in mine:
            f = tk.Frame(self.assigned, bg=GAME_BG.get(r["game"], GAME_BG["마크"]))
            f.pack(fill="x", padx=10, pady=2)
            tk.Label(f, text=bmp(r["title"]), fg="#ffffff", bg=f["bg"], font=(FONT, 10, "bold"), anchor="w",
                     justify="left", wraplength=380).pack(side="left", padx=8, pady=5, fill="x", expand=True)
            tk.Button(f, text="빼기", command=lambda r=r: self.app.assign(r, None), font=(FONT, 9), relief="flat",
                      bg="#263238", fg="#ffffff", activebackground="#37474f").pack(side="right", padx=6)
        shown, hidden = self.render_filters()
        if not shown:
            tk.Label(self.inner, text="띄울 후보가 없습니다", fg="#b0bec5", bg=POP_BG, font=(FONT, 10)).pack(pady=20)
        status = object()
        for r in shown:
            if r["status"] != status:  # 상태별 소제목
                status = r["status"]
                tk.Label(self.inner, text=f"{status or '상태 없음'} · {sum(x['status'] == status for x in shown)}",
                         bg=STATUS_BG.get(status, "#424242"), fg="#ffffff", font=(FONT, 9, "bold"),
                         padx=6).pack(anchor="w", pady=(8, 2))
            f = tk.Frame(self.inner, bg=ROW_BG, cursor="hand2")
            f.pack(fill="x", pady=2)
            parts = []
            if self.game == "전체" and r["game"]:
                parts.append(tk.Label(f, text=r["game"], bg=GAME_BG.get(r["game"], "#424242"), fg="#ffffff",
                                      font=(FONT, 8, "bold"), padx=4))
                parts[-1].pack(side="left", padx=(6, 0), pady=7)
            extra = ([f"×{r['ratio']:.1f}"] if r["ratio"] else []) + \
                    ([f"{int(r['shoot'][5:7])}/{int(r['shoot'][8:])} 배정"] if r["shoot"] else [])
            parts.append(tk.Label(f, text="  ".join(extra), bg=ROW_BG, fg="#b0bec5", font=(FONT, 9)))
            parts[-1].pack(side="right", padx=6)
            parts.append(tk.Label(f, text=bmp(r["title"]), bg=ROW_BG, fg="#ffffff", font=(FONT, 10), anchor="w",
                                  justify="left", wraplength=300))
            parts[-1].pack(side="left", fill="x", expand=True, padx=(6, 0), pady=6)
            hover = [f] + [p for p in parts if p["bg"] == ROW_BG]
            for wdg in [f] + parts:
                wdg.bind("<Enter>", lambda e, ws=hover: [w.config(bg=ROW_HOVER) for w in ws])
                wdg.bind("<Leave>", lambda e, ws=hover: [w.config(bg=ROW_BG) for w in ws])
                wdg.bind("<Button-1>", lambda e, r=r: self.app.assign(r, self.iso))
        if hidden:
            tk.Label(self.inner, text=f"{hidden} 숨김 — 위 「단계」 버튼을 누르면 보임", fg="#b0bec5", bg=POP_BG,
                     font=(FONT, 9)).pack(pady=10)
        self.cv.yview_moveto(0)

    def render_filters(self):
        """게임 버튼(하나 고름, 노션 값으로 자동)·단계 버튼(여러 개 켬) → (보일 행, 숨긴 개수 글)"""
        pool = candidates(self.app.rows, self.day)
        rank = {g: i for i, g in enumerate(GAME_ORDER)}
        games = sorted({r["game"] for r in pool}, key=lambda g: (rank.get(g, len(rank)), str(g)))
        if self.game != "전체" and self.game not in games:
            self.game = "전체"
        r1 = tk.Frame(self.filters, bg=POP_BG)
        r1.pack(fill="x", padx=10, pady=(8, 0))
        tk.Label(r1, text="게임", fg="#b0bec5", bg=POP_BG, font=(FONT, 9), width=4, anchor="w").pack(side="left")
        self.chip(r1, f"전체 {len(pool)}", self.game == "전체", lambda: self.set_game("전체"))
        for g in games:
            self.chip(r1, f"{g or '게임 없음'} {sum(r['game'] == g for r in pool)}", self.game == g,
                      lambda g=g: self.set_game(g), GAME_BG.get(g))
        in_game = [r for r in pool if self.game == "전체" or r["game"] == self.game]
        r2 = tk.Frame(self.filters, bg=POP_BG)
        r2.pack(fill="x", padx=10, pady=(4, 0))
        tk.Label(r2, text="단계", fg="#b0bec5", bg=POP_BG, font=(FONT, 9), width=4, anchor="w").pack(side="left")
        count = {name: sum(stage_of(r["status"]) == name for r in in_game) for name, _ in STAGES}
        for name, _ in STAGES:
            self.chip(r2, f"{name} {count[name]}", name in self.app.stages, lambda name=name: self.toggle(name))
        shown = [r for r in in_game if stage_of(r["status"]) in self.app.stages]
        hidden = ", ".join(f"{n} {count[n]}개" for n, _ in STAGES if n not in self.app.stages and count[n])
        return shown, hidden

    def chip(self, parent, text, on, cmd, color=None):
        bg = (color or "#eceff1") if on else ROW_BG
        fg = ("#ffffff" if color else "#202124") if on else "#b0bec5"
        c = tk.Label(parent, text=text, bg=bg, fg=fg, font=(FONT, 9, "bold" if on else "normal"), padx=8, pady=2,
                     cursor="hand2")
        c.bind("<Button-1>", lambda e: cmd())
        c.pack(side="left", padx=2)

    def set_game(self, g):
        self.game = g
        self.render()

    def toggle(self, name):
        self.app.stages ^= {name}
        self.render()

    def swatch(self, parent, c, into, text=""):
        s = tk.Label(parent, width=2, bg=c or POP_BG, text=text, fg="#ffffff", font=(FONT, 8), relief="flat", bd=0,
                     highlightthickness=2, cursor="hand2")
        # 색은 채도 막대로 바뀌니 누를 때 그 칸의 지금 색을 찾는다
        s.bind("<Button-1>", lambda e: self.choose(next(k for k, w in self.swatches + self.gen_swatches if w is s)))
        s.pack(side="left", padx=2, ipady=2, ipadx=4 if text else 0)
        into.append((c, s))

    def render_swatches(self):
        """둘째·셋째 줄 = 채도 막대 값으로 만든 색(밝게 / 진하게). 칸은 처음 한 번만 만들고 막대를 움직이면
        색만 바꾼다 — 칸 32개를 매번 새로 만들면 한 칸에 42~153ms라 끊겼다(10-27 실측)"""
        sat = self.sat.get()
        colors = [c for m in SWATCH_LUM for c in white_text_colors(sat / 100, m)]
        if not self.gen_swatches:
            for i, c in enumerate(colors):
                if i % len(SWATCH_HUES) == 0:
                    row = tk.Frame(self.gen, bg=POP_BG)
                    row.pack(fill="x", pady=1)
                self.swatch(row, c, self.gen_swatches)
        else:
            for i, c in enumerate(colors):
                self.gen_swatches[i][1].config(bg=c)
                self.gen_swatches[i] = (c, self.gen_swatches[i][1])
        self.mark()

    def save_sat(self):
        if self.app.cfg.get("swatch_sat") != self.sat.get():
            self.app.cfg["swatch_sat"] = self.sat.get()
            jsave("config.json", self.app.cfg)

    def custom(self):
        _, hexc = colorchooser.askcolor(color=self.bg or GAME_BG["마크"], parent=self.top, title="칸 색 직접 고르기")
        if hexc:
            self.choose(hexc)  # 칠하면 '최근' 줄에 들어간다

    def mark(self):
        for k, s in self.swatches + self.gen_swatches:
            on = k == self.bg
            s.config(highlightbackground="#ffffff" if on else POP_BG, highlightcolor="#ffffff" if on else POP_BG)

    def choose(self, c):
        """색은 누르자마자 칸에 — 1초 기다리기(schedule)는 메모 칠 때만(10-27 사용자 「적용되는게 느린데」, 실측 1015ms)"""
        self.bg = c
        self.mark()
        if self._pending:
            self.top.after_cancel(self._pending)
        self.flush()  # 바뀐 게 없으면 아무것도 안 쓴다(창을 처음 열 때 포함)

    def schedule(self):
        if self._pending:
            self.top.after_cancel(self._pending)
        self._pending = self.top.after(1000, self.flush)

    def flush(self):
        """바뀐 메모·색을 저장. 실패하면 창에 알리고 False"""
        self._pending = None
        text = self.text.get("1.0", "end").strip()
        if (text, self.bg) == self.orig:
            return True
        try:
            self.app.save_cell(self.iso, text, self.bg)
        except OSError as e:
            log(f"메모 저장 실패: {e}")
            self.set_status(f"메모 저장 실패: {e} — 창을 닫지 않았습니다", "#ff8a80")
            return False
        if self.bg and self.bg != self.orig[1]:
            self.app.note_color(self.bg)
        self.orig = (text, self.bg)
        return True

    def save(self):
        self.close()

    def close(self):
        """Esc·닫기·창 닫기·후보를 골라 닫힐 때·달력을 끝낼 때 모두 바뀐 메모·색을 저장한다.
        저장이 실패하면 창을 닫지 않는다(Codex desk-cal-gap 6)"""
        if self.top.winfo_exists():
            if self._pending:
                self.top.after_cancel(self._pending)
            if not self.flush():
                return
            self.save_sat()  # 막대를 키보드로 움직였거나 손 뗌을 놓쳤을 때
            self.top.destroy()
        if self.app.popup is self:
            self.app.popup = None


class MonthPicker:
    """달력 제목을 누르면 뜨는 연·월 바로 가기(윈도우 달력처럼) — ‹ 연도 › + 1~12월"""

    def __init__(self, app, x, y):
        self.app, self.year = app, app.month.year
        t = self.top = tk.Toplevel(app.root)
        t.overrideredirect(True)
        t.attributes("-topmost", True)
        t.configure(bg=HEAD, highlightthickness=1, highlightbackground="#8a9499")
        t.geometry(f"250x205+{x}+{y}")
        t.bind("<Escape>", lambda e: t.destroy())
        t.bind("<FocusOut>", lambda e: t.after(150, self.close_if_away))
        t.bind("<MouseWheel>", lambda e: self.step(-1 if e.delta > 0 else 1))
        self.render()
        t.focus_force()

    def close_if_away(self):
        if self.top.winfo_exists() and self.top.focus_get() is None:
            self.top.destroy()

    def step(self, n):
        self.year += n
        self.render()

    def render(self):
        t = self.top
        for w in t.winfo_children():
            w.destroy()
        bar = tk.Frame(t, bg=HEAD)
        bar.pack(fill="x", pady=(6, 4))
        for text, n, side in (("‹", -1, "left"), ("›", 1, "right")):
            b = tk.Label(bar, text=text, fg="#ffffff", bg=HEAD, font=(FONT, 14, "bold"), padx=12, cursor="hand2")
            b.bind("<Button-1>", lambda e, n=n: self.step(n))
            b.pack(side=side)
        tk.Label(bar, text=f"{self.year}년", fg="#fff3c4", bg=HEAD, font=(FONT, 12, "bold")).pack()
        grid = tk.Frame(t, bg=HEAD)
        grid.pack(padx=8, pady=(0, 8))
        today = dt.date.today()
        for m in range(1, 13):
            cur = (self.year, m) == (self.app.month.year, self.app.month.month)
            now = (self.year, m) == (today.year, today.month)
            b = tk.Label(grid, text=f"{m}월", width=5, pady=6, cursor="hand2", font=(FONT, 10, "bold" if cur else "normal"),
                         bg="#eceff1" if cur else ROW_BG, fg="#202124" if cur else "#ffffff",
                         highlightthickness=1, highlightbackground=TODAY if now else HEAD)
            b.bind("<Button-1>", lambda e, m=m: self.go(m))
            b.grid(row=(m - 1) // 4, column=(m - 1) % 4, padx=2, pady=2)

    def go(self, m):
        self.app.month = dt.date(self.year, m, 1)
        self.app.draw()
        self.top.destroy()


class Settings:
    """⚙ 달력 설정 — 날짜 숫자·칸 글씨 글꼴/크기/굵게/색, 오늘 테두리 색. 바꾸면 바로 적용·저장(config.json)"""

    def __init__(self, app):
        self.app = app
        t = self.top = tk.Toplevel(app.root)
        t.title("달력 설정")
        t.geometry(f"+{app.rect[0] + app.rect[2] - 520}+{app.rect[1] + 48}")  # ⚙ 바로 아래
        t.configure(bg=POP_BG, padx=12, pady=10)
        t.attributes("-topmost", True)
        t.resizable(False, False)
        fams = sorted(f for f in tkfont.families(app.root) if not f.startswith("@"))
        self.rows = {}
        for r, (key, label) in enumerate((("date", "날짜 숫자"), ("memo", "칸 글씨"))):
            fam, size, bold, color = app.fonts()[key]
            tk.Label(t, text=label, fg="#ffffff", bg=POP_BG, font=(FONT, 10)).grid(row=r, column=0, sticky="w", pady=4)
            fv, sv, bv = tk.StringVar(value=fam), tk.IntVar(value=size), tk.BooleanVar(value=bold)
            cb = ttk.Combobox(t, textvariable=fv, values=fams, width=26, state="readonly")
            cb.bind("<<ComboboxSelected>>", lambda e: self.apply())
            cb.grid(row=r, column=1, padx=6)
            tk.Spinbox(t, from_=6, to=28, textvariable=sv, width=4, command=self.apply).grid(row=r, column=2)
            tk.Checkbutton(t, text="굵게", variable=bv, command=self.apply, fg="#ffffff", bg=POP_BG, selectcolor=POP_BG,
                           activebackground=POP_BG, activeforeground="#ffffff").grid(row=r, column=3, padx=6)
            btn = tk.Button(t, text="  색  ", bg=color, relief="flat", command=lambda key=key: self.pick(key))
            btn.grid(row=r, column=4)
            self.rows[key] = [fv, sv, bv, color, btn]
        tk.Label(t, text="오늘 테두리", fg="#ffffff", bg=POP_BG, font=(FONT, 10)).grid(row=2, column=0, sticky="w", pady=4)
        self.today = app.fonts()["today"]
        self.today_btn = tk.Button(t, text="  색  ", bg=self.today, relief="flat", command=lambda: self.pick("today"))
        self.today_btn.grid(row=2, column=4)
        tk.Label(t, text="칸 투명도 %", fg="#ffffff", bg=POP_BG, font=(FONT, 10)).grid(row=3, column=0, sticky="w")
        self.alpha = tk.IntVar(value=int(app.cfg.get("alpha", 0)))
        tk.Scale(t, from_=0, to=60, orient="horizontal", variable=self.alpha, command=lambda v: self.apply(),
                 length=220, bg=POP_BG, fg="#ffffff", highlightthickness=0, troughcolor=ROW_BG).grid(
            row=3, column=1, sticky="w", padx=6)
        tk.Label(t, text="글씨도 같이 옅어짐 · 바탕화면이 단색이면 0이 DesktopCal과 같은 색", fg="#b0bec5", bg=POP_BG,
                 font=(FONT, 8)).grid(row=4, column=1, columnspan=4, sticky="w", padx=6)
        self.terms, self.days = (tk.BooleanVar(value=app.cfg.get(k, True)) for k in ("show_terms", "show_days"))
        opts = tk.Frame(t, bg=POP_BG)
        opts.grid(row=5, column=1, columnspan=4, sticky="w", padx=2, pady=(6, 0))
        for text, var in (("24절기 표시", self.terms), ("기념일 표시", self.days)):
            tk.Checkbutton(opts, text=text, variable=var, command=self.apply, fg="#ffffff", bg=POP_BG,
                           selectcolor=POP_BG, activebackground=POP_BG, activeforeground="#ffffff").pack(side="left")
        # 노션 연결·위치(10-27 exe 배포판 — 조나스 PC엔 .env도 DesktopCal 자리도 없다). 토큰은 이 PC config.json에만
        n = app.cfg.get("notion") or {}
        self.entries = {}
        for r, (key, label, val) in enumerate((("token", "노션 토큰", n.get("token", "")),
                                               ("db", "후보 표 링크", n.get("db", "")),
                                               ("rect", "위치 X,Y,W,H", ",".join(map(str, app.rect)))), start=6):
            tk.Label(t, text=label, fg="#ffffff", bg=POP_BG, font=(FONT, 10)).grid(
                row=r, column=0, sticky="w", pady=(10 if r == 6 else 4, 0))
            e = self.entries[key] = tk.Entry(t, width=46, show="•" if key == "token" else "")
            e.insert(0, val)
            e.grid(row=r, column=1, columnspan=3, sticky="w", padx=6, pady=(10 if r == 6 else 4, 0))
        tk.Button(t, text="연결", command=self.connect, font=(FONT, 9), relief="flat", bg="#455a64", fg="#ffffff",
                  padx=10).grid(row=7, column=4, pady=(4, 0))
        tk.Button(t, text="옮기기", command=self.move, font=(FONT, 9), relief="flat", bg="#455a64", fg="#ffffff",
                  padx=4).grid(row=8, column=4, pady=(4, 0))
        self.note = tk.Label(t, text="", fg="#b0bec5", bg=POP_BG, font=(FONT, 8))
        self.note.grid(row=9, column=1, columnspan=4, sticky="w", padx=6)
        bar = tk.Frame(t, bg=POP_BG)
        bar.grid(row=10, column=0, columnspan=5, sticky="e", pady=(10, 0))
        tk.Label(bar, text=f"v{VERSION}", fg="#78909c", bg=POP_BG, font=(FONT, 8)).pack(side="left", padx=8)
        tk.Button(bar, text="DesktopCal 글꼴로 되돌리기", command=self.reset, font=(FONT, 9), relief="flat",
                  bg="#455a64", fg="#ffffff").pack(side="left", padx=4)
        tk.Button(bar, text="닫기", command=t.destroy, font=(FONT, 9), relief="flat", bg="#455a64",
                  fg="#ffffff", padx=12).pack(side="left")

    def pick(self, key):
        cur = self.today if key == "today" else self.rows[key][3]
        rgb, hexc = colorchooser.askcolor(color=cur, parent=self.top, title="색 고르기")
        if not hexc:
            return
        if key == "today":
            self.today = hexc
            self.today_btn.config(bg=hexc)
        else:
            self.rows[key][3] = hexc
            self.rows[key][4].config(bg=hexc)
        self.apply()

    def apply(self):
        fonts = {"today": self.today}
        for key, (fv, sv, bv, color, _) in self.rows.items():
            try:
                size = int(sv.get())
            except (tk.TclError, ValueError):
                return  # 크기 칸을 고치는 중
            fonts[key] = [fv.get(), size, bool(bv.get()), color]
        self.app.cfg["fonts"] = fonts
        if hasattr(self, "days"):  # 창을 다 그리기 전(색 고르기 등)엔 글꼴만
            self.app.cfg.update(alpha=int(self.alpha.get()), show_terms=bool(self.terms.get()),
                                show_days=bool(self.days.get()))
            self.app.apply_alpha()
        jsave("config.json", self.app.cfg)
        self.app.draw()

    def connect(self):
        tok = self.entries["token"].get().strip()
        m = re.search(r"(?<![0-9a-f])([0-9a-f]{32}|[0-9a-f]{8}(?:-[0-9a-f]{4}){3}-[0-9a-f]{12})(?![0-9a-f])",
                      self.entries["db"].get().lower())
        if not (tok and m):
            self.note.config(text="토큰과 후보 표 링크(또는 id 32자)를 둘 다 넣어 주세요", fg="#ff8a80")
            return
        self.app.cfg["notion"] = {"token": tok, "db": m.group(1).replace("-", "")}
        jsave("config.json", self.app.cfg)
        _ENV.clear()
        self.app.sync()
        self.note.config(text="저장함 — 달력 왼쪽 위에 「노션 … 기준」이 뜨면 연결된 것", fg="#b0bec5")

    def move(self):
        try:
            r = [int(v) for v in self.entries["rect"].get().split(",")]
        except ValueError:
            r = []
        if len(r) != 4 or r[2] < 400 or r[3] < 300:
            self.note.config(text="위치는 X,Y,너비,높이 숫자 4개(너비 400·높이 300 이상)", fg="#ff8a80")
            return
        self.app.cfg["rect"] = r
        jsave("config.json", self.app.cfg)
        self.top.destroy()
        self.app.stop(restart=True)

    def reset(self):
        got = {**DEFAULT_FONTS, **import_fonts()}
        for key in ("date", "memo"):
            fam, size, bold, color = got[key]
            fv, sv, bv, _, btn = self.rows[key]
            fv.set(fam), sv.set(size), bv.set(bold)
            self.rows[key][3] = color
            btn.config(bg=color)
        self.apply()


def set_autostart(on):
    import winreg
    key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE)
    with key:
        if on and FROZEN:
            winreg.SetValueEx(key, "NabuDeskCal", 0, winreg.REG_SZ, f'"{INSTALL}"')
        elif on:
            pyw = Path(sys.executable).with_name("pythonw.exe")
            winreg.SetValueEx(key, "NabuDeskCal", 0, winreg.REG_SZ, f'"{pyw}" "{Path(__file__).resolve()}"')
        else:
            try:
                winreg.DeleteValue(key, "NabuDeskCal")
            except FileNotFoundError:
                pass
    print("자동 실행", "등록" if on else "해제")


def main():
    ap = argparse.ArgumentParser(description="바탕화면 달력 + 노션 긴영상 후보")
    ap.add_argument("--at", help="X,Y,W,H")
    ap.add_argument("--autostart", choices=["on", "off"])
    a = ap.parse_args()
    if a.autostart:
        return set_autostart(a.autostart == "on")
    if FROZEN and Path(sys.executable).resolve() != INSTALL.resolve():
        return install()
    if FROZEN:
        try:
            INSTALL.with_name("desk_cal.old.exe").unlink(missing_ok=True)  # 지난 업데이트 때 이름 바꿔 둔 옛 exe
        except OSError:
            pass
    global MUTEX  # 데이터 폴더마다 하나 — 시험용 APPDATA로 띄운 것과 안 겹치게. 업데이트로 다시 띄울 때 놓는다
    MUTEX = k32.CreateMutexW(None, False, f"Local\\nabu-desk-cal-{zlib.crc32(str(DATA).lower().encode()):08x}")
    if ctypes.get_last_error() == 183:
        if FROZEN:
            u.MessageBoxW(None, "달력이 이미 켜져 있어요.", "바탕화면 달력", 0x40)
        print("이미 실행 중")
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except OSError:
        pass
    cfg = jload("config.json", {})
    baks = sorted((DATA / "backup").glob("cells_*.json"))
    if not (DATA / "cells.json").exists() and baks:  # DesktopCal 옛 상태로 조용히 되돌아가지 않게
        shutil.copyfile(baks[-1], DATA / "cells.json")
        log(f"cells.json 없음 — 백업 {baks[-1].name}에서 되살림")
    if not (DATA / "cells.json").exists():
        cells, holidays, palette = import_desktopcal()
        jsave("cells.json", cells)
        jsave("holidays.json", holidays)
        cfg["palette"] = palette + [c for c in (WEEKEND, GAME_BG["GTA"], GAME_BG["공통"]) if c not in palette]
        log(f"DesktopCal에서 가져옴: 칸 {len(cells)} · 공휴일 {len(holidays)} · 색 {len(palette)}")
    backup_cells()
    if "fonts" not in cfg:  # 10-27 사용자 「전 달력에 있던 설정들이 없는데」 — DesktopCal 글꼴부터 그대로
        cfg["fonts"] = {**DEFAULT_FONTS, **import_fonts()}
        log(f"DesktopCal 글꼴 가져옴: {cfg['fonts']}")
    if a.at:
        cfg["rect"] = [int(v) for v in a.at.split(",")]
    if "rect" not in cfg:
        lv = desktop_listview()
        cfg["rect"] = list((lv and dkcal_rect(lv)) or default_rect())
    jsave("config.json", cfg)
    while True:
        try:
            app = DeskCal(cfg)
            app.root.mainloop()
        except Exception:
            log("달력 오류 — 1분 뒤 다시 만든다\n" + traceback.format_exc())
            time.sleep(60)
            continue
        if app.relaunch:
            k32.CloseHandle(MUTEX)
            relaunch()
            break
        if app.quit:
            break
        time.sleep(3)  # 탐색기가 다시 뜰 시간


if __name__ == "__main__":
    main()
