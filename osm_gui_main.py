#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
OSM Overpass API 数据下载工具
Tkinter GUI + PostgreSQL 存储 + Shapefile 导出
独立工具 — 与高德 POI 爬虫无依赖关系
"""

import json
import os
import sys
import time
import queue
import threading
import math
import traceback
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from datetime import datetime

import requests
import psycopg2
import shapefile as shp

# ============================================================
# 路径工具
# ============================================================

def _get_app_dir():
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

# ============================================================
# 常量
# ============================================================

OVERPASS_URL = "https://overpass-api.de/api/interpreter"
USER_AGENT = "OSMDataDownloader/1.0 (GIS-tool)"

# 中国各省/直辖市/自治区 bbox (WGS84) — 无需联网，即时查询
CN_PROVINCES = {
    "河南":  {"south": 31.38, "north": 36.37, "west": 110.35, "east": 116.64},
    "河北":  {"south": 36.05, "north": 42.62, "west": 113.45, "east": 119.84},
    "北京":  {"south": 39.44, "north": 41.06, "west": 115.42, "east": 117.50},
    "天津":  {"south": 38.56, "north": 40.25, "west": 116.70, "east": 118.06},
    "上海":  {"south": 30.69, "north": 31.87, "west": 120.85, "east": 122.00},
    "重庆":  {"south": 28.16, "north": 32.22, "west": 105.29, "east": 110.20},
    "山东":  {"south": 34.38, "north": 38.40, "west": 114.80, "east": 122.72},
    "山西":  {"south": 34.57, "north": 40.74, "west": 110.23, "east": 114.55},
    "陕西":  {"south": 31.70, "north": 39.58, "west": 105.49, "east": 111.25},
    "甘肃":  {"south": 32.60, "north": 42.80, "west": 92.21, "east": 108.72},
    "青海":  {"south": 31.54, "north": 38.96, "west": 89.42, "east": 103.06},
    "四川":  {"south": 26.05, "north": 34.31, "west": 97.35, "east": 108.54},
    "湖北":  {"south": 29.03, "north": 33.27, "west": 108.37, "east": 116.13},
    "湖南":  {"south": 24.62, "north": 30.13, "west": 108.78, "east": 114.25},
    "江苏":  {"south": 30.75, "north": 35.13, "west": 116.35, "east": 121.95},
    "安徽":  {"south": 29.41, "north": 34.65, "west": 114.88, "east": 119.65},
    "浙江":  {"south": 27.17, "north": 31.18, "west": 118.02, "east": 122.95},
    "江西":  {"south": 24.48, "north": 30.08, "west": 113.57, "east": 118.48},
    "福建":  {"south": 23.55, "north": 28.32, "west": 115.85, "east": 120.72},
    "广东":  {"south": 20.22, "north": 25.52, "west": 109.65, "east": 117.32},
    "广西":  {"south": 21.40, "north": 26.38, "west": 104.45, "east": 112.07},
    "云南":  {"south": 21.13, "north": 29.25, "west": 97.53, "east": 106.20},
    "贵州":  {"south": 24.62, "north": 29.22, "west": 103.60, "east": 109.60},
    "海南":  {"south": 18.16, "north": 20.17, "west": 108.61, "east": 111.05},
    "辽宁":  {"south": 38.72, "north": 43.49, "west": 118.88, "east": 125.78},
    "吉林":  {"south": 40.85, "north": 46.30, "west": 121.64, "east": 131.30},
    "黑龙江":{"south": 43.42, "north": 53.56, "west": 121.18, "east": 135.09},
    "内蒙古":{"south": 37.40, "north": 53.33, "west": 97.20, "east": 126.07},
    "宁夏":  {"south": 35.23, "north": 39.38, "west": 104.28, "east": 107.65},
    "新疆":  {"south": 34.42, "north": 49.18, "west": 73.50, "east": 96.40},
    "西藏":  {"south": 26.85, "north": 36.58, "west": 78.40, "east": 99.12},
    "台湾":  {"south": 21.90, "north": 25.30, "west": 120.00, "east": 122.00},
    "香港":  {"south": 22.15, "north": 22.56, "west": 113.83, "east": 114.40},
    "澳门":  {"south": 22.11, "north": 22.22, "west": 113.53, "east": 113.60},
}

# 国外国家/地区及其省份/州 bbox (WGS84)
WORLD_REGIONS = {
    "日本": {
        "bbox": {"south": 24.05, "north": 45.55, "west": 122.93, "east": 153.99},
        "provinces": {
            "东京都": {"south": 35.53, "north": 35.90, "west": 138.94, "east": 139.92},
            "东京23区": {"south": 35.53, "north": 35.82, "west": 139.56, "east": 139.92},
            "大阪府": {"south": 34.36, "north": 34.93, "west": 135.08, "east": 135.68},
            "京都府": {"south": 34.70, "north": 35.68, "west": 135.00, "east": 136.02},
            "北海道": {"south": 41.35, "north": 45.56, "west": 139.33, "east": 145.82},
            "爱知县": {"south": 34.67, "north": 35.43, "west": 136.67, "east": 137.65},
            "福冈县": {"south": 33.01, "north": 33.75, "west": 130.03, "east": 131.02},
            "神奈川县": {"south": 35.10, "north": 35.63, "west": 138.93, "east": 139.82},
            "冲绳县": {"south": 24.05, "north": 27.08, "west": 122.93, "east": 128.32},
        }
    },
    "韩国": {
        "bbox": {"south": 33.10, "north": 38.62, "west": 124.60, "east": 131.87},
        "provinces": {
            "首尔特别市": {"south": 37.42, "north": 37.69, "west": 126.76, "east": 127.18},
            "京畿道": {"south": 36.94, "north": 38.14, "west": 126.07, "east": 127.72},
            "釜山广域市": {"south": 34.99, "north": 35.30, "west": 128.89, "east": 129.28},
            "仁川广域市": {"south": 37.37, "north": 37.63, "west": 126.37, "east": 126.80},
            "济州特别自治道": {"south": 33.10, "north": 33.56, "west": 126.13, "east": 126.98},
            "江原道": {"south": 37.04, "north": 38.62, "west": 127.10, "east": 129.40},
        }
    },
    "美国": {
        "bbox": {"south": 24.52, "north": 49.38, "west": -124.77, "east": -66.95},
        "provinces": {
            "加利福尼亚州": {"south": 32.53, "north": 42.01, "west": -124.42, "east": -114.13},
            "纽约州": {"south": 40.49, "north": 45.02, "west": -79.76, "east": -71.86},
            "德克萨斯州": {"south": 25.84, "north": 36.50, "west": -106.65, "east": -93.51},
            "佛罗里达州": {"south": 24.52, "north": 31.00, "west": -87.63, "east": -80.03},
            "伊利诺伊州": {"south": 36.97, "north": 42.51, "west": -91.51, "east": -87.02},
            "华盛顿州": {"south": 45.54, "north": 49.00, "west": -124.79, "east": -116.92},
            "马萨诸塞州": {"south": 41.24, "north": 42.89, "west": -73.50, "east": -69.93},
            "内华达州": {"south": 35.00, "north": 42.00, "west": -120.00, "east": -114.04},
            "夏威夷州": {"south": 18.91, "north": 28.40, "west": -178.33, "east": -154.81},
            "佐治亚州": {"south": 30.36, "north": 35.00, "west": -85.61, "east": -80.84},
        }
    },
    "英国": {
        "bbox": {"south": 49.90, "north": 58.67, "west": -8.17, "east": 1.76},
        "provinces": {
            "英格兰": {"south": 49.95, "north": 55.80, "west": -5.72, "east": 1.76},
            "苏格兰": {"south": 54.63, "north": 58.67, "west": -8.17, "east": -0.73},
            "威尔士": {"south": 51.38, "north": 53.43, "west": -5.26, "east": -2.65},
            "北爱尔兰": {"south": 54.01, "north": 55.31, "west": -8.17, "east": -5.43},
        }
    },
    "德国": {
        "bbox": {"south": 47.27, "north": 55.06, "west": 5.87, "east": 15.04},
        "provinces": {
            "柏林": {"south": 52.34, "north": 52.68, "west": 13.09, "east": 13.77},
            "拜仁州": {"south": 47.27, "north": 50.56, "west": 8.97, "east": 13.84},
            "巴登-符腾堡州": {"south": 47.53, "north": 49.79, "west": 7.51, "east": 10.50},
            "北莱茵-威斯特法伦州": {"south": 50.32, "north": 52.53, "west": 5.87, "east": 9.33},
            "黑森州": {"south": 49.39, "north": 51.66, "west": 7.77, "east": 10.24},
            "汉堡": {"south": 53.39, "north": 53.75, "west": 9.73, "east": 10.33},
        }
    },
    "法国": {
        "bbox": {"south": 42.33, "north": 51.12, "west": -4.79, "east": 8.23},
        "provinces": {
            "法兰西岛": {"south": 48.12, "north": 49.24, "west": 1.45, "east": 2.86},
            "奥弗涅-罗讷-阿尔卑斯": {"south": 44.18, "north": 46.53, "west": 2.74, "east": 7.10},
            "普罗旺斯-阿尔卑斯-蔚蓝海岸": {"south": 42.98, "north": 45.12, "west": 4.23, "east": 7.72},
            "新阿基坦": {"south": 42.77, "north": 47.16, "west": -1.79, "east": 2.56},
            "布列塔尼": {"south": 47.29, "north": 48.90, "west": -4.79, "east": -1.00},
            "大东部": {"south": 47.59, "north": 50.18, "west": 4.04, "east": 8.23},
        }
    },
    "加拿大": {
        "bbox": {"south": 41.68, "north": 83.11, "west": -141.00, "east": -52.62},
        "provinces": {
            "安大略省": {"south": 41.68, "north": 56.85, "west": -95.15, "east": -74.34},
            "魁北克省": {"south": 44.99, "north": 62.59, "west": -79.76, "east": -57.10},
            "不列颠哥伦比亚省": {"south": 48.22, "north": 60.00, "west": -139.06, "east": -114.05},
            "艾伯塔省": {"south": 48.99, "north": 60.00, "west": -120.00, "east": -110.00},
        }
    },
    "澳大利亚": {
        "bbox": {"south": -43.64, "north": -10.69, "west": 112.92, "east": 153.64},
        "provinces": {
            "新南威尔士州": {"south": -37.51, "north": -28.15, "west": 140.99, "east": 153.64},
            "维多利亚州": {"south": -39.14, "north": -33.98, "west": 140.96, "east": 149.98},
            "昆士兰州": {"south": -29.18, "north": -10.69, "west": 137.99, "east": 153.55},
            "西澳大利亚州": {"south": -35.13, "north": -13.87, "west": 112.92, "east": 129.00},
            "南澳大利亚州": {"south": -38.06, "north": -26.00, "west": 129.00, "east": 141.00},
        }
    },
    "意大利": {
        "bbox": {"south": 36.65, "north": 47.09, "west": 6.63, "east": 18.52},
        "provinces": {
            "拉齐奥": {"south": 40.78, "north": 42.84, "west": 11.45, "east": 14.03},
            "伦巴第": {"south": 44.68, "north": 46.62, "west": 8.49, "east": 11.36},
            "威尼托": {"south": 44.83, "north": 46.68, "west": 10.63, "east": 13.10},
            "托斯卡纳": {"south": 42.24, "north": 44.47, "west": 9.69, "east": 12.37},
            "西西里": {"south": 36.65, "north": 38.30, "west": 12.43, "east": 15.65},
        }
    },
    "西班牙": {
        "bbox": {"south": 36.00, "north": 43.79, "west": -9.30, "east": 4.33},
        "provinces": {
            "马德里自治区": {"south": 39.88, "north": 41.16, "west": -4.58, "east": -3.05},
            "加泰罗尼亚": {"south": 40.52, "north": 42.86, "west": 0.16, "east": 3.33},
            "安达卢西亚": {"south": 36.00, "north": 38.72, "west": -7.52, "east": -1.63},
            "瓦伦西亚": {"south": 37.84, "north": 40.80, "west": -1.55, "east": 0.75},
            "巴斯克": {"south": 42.48, "north": 43.46, "west": -3.46, "east": -1.72},
        }
    },
    "巴西": {
        "bbox": {"south": -33.75, "north": 5.27, "west": -73.99, "east": -34.79},
        "provinces": {
            "圣保罗州": {"south": -25.36, "north": -19.78, "west": -53.11, "east": -44.16},
            "里约热内卢州": {"south": -23.37, "north": -20.77, "west": -44.89, "east": -40.96},
            "米纳斯吉拉斯州": {"south": -22.92, "north": -14.24, "west": -51.04, "east": -39.86},
            "巴伊亚州": {"south": -18.35, "north": -8.54, "west": -46.62, "east": -37.34},
            "巴拉那州": {"south": -26.72, "north": -22.51, "west": -54.62, "east": -47.89},
            "亚马逊州": {"south": -9.82, "north": 2.25, "west": -73.99, "east": -56.10},
        }
    },
    "印度": {
        "bbox": {"south": 6.75, "north": 35.50, "west": 68.11, "east": 97.40},
        "provinces": {
            "马哈拉施特拉邦": {"south": 15.60, "north": 22.03, "west": 72.64, "east": 80.93},
            "德里国家首都辖区": {"south": 28.40, "north": 28.93, "west": 76.84, "east": 77.35},
            "卡纳塔克邦": {"south": 11.57, "north": 18.48, "west": 74.05, "east": 78.59},
            "泰米尔纳德邦": {"south": 8.08, "north": 13.57, "west": 76.19, "east": 80.35},
            "北方邦": {"south": 23.87, "north": 30.40, "west": 77.08, "east": 84.63},
            "西孟加拉邦": {"south": 21.54, "north": 27.24, "west": 85.83, "east": 89.87},
        }
    },
    "泰国": {
        "bbox": {"south": 5.62, "north": 20.46, "west": 97.34, "east": 105.64},
        "provinces": {
            "曼谷": {"south": 13.52, "north": 13.96, "west": 100.32, "east": 100.86},
            "清迈府": {"south": 17.23, "north": 20.10, "west": 97.34, "east": 100.13},
            "普吉府": {"south": 7.56, "north": 8.20, "west": 98.21, "east": 98.43},
            "春武里府": {"south": 12.56, "north": 13.44, "west": 100.81, "east": 101.42},
            "素叻他尼府": {"south": 8.47, "north": 9.78, "west": 98.60, "east": 99.85},
        }
    },
    "越南": {
        "bbox": {"south": 8.56, "north": 23.39, "west": 102.14, "east": 109.47},
        "provinces": {
            "河内市": {"south": 20.67, "north": 21.39, "west": 105.58, "east": 106.07},
            "胡志明市": {"south": 10.43, "north": 11.15, "west": 106.39, "east": 106.98},
            "岘港市": {"south": 15.97, "north": 16.28, "west": 107.98, "east": 108.35},
            "庆和省": {"south": 11.72, "north": 12.85, "west": 108.63, "east": 109.47},
            "广宁省": {"south": 20.67, "north": 21.62, "west": 106.42, "east": 108.07},
        }
    },
    "印度尼西亚": {
        "bbox": {"south": -11.00, "north": 5.90, "west": 95.01, "east": 141.02},
        "provinces": {
            "雅加达首都特区": {"south": -6.37, "north": -5.87, "west": 106.66, "east": 106.98},
            "巴厘省": {"south": -8.85, "north": -8.00, "west": 114.43, "east": 115.71},
            "东爪哇省": {"south": -8.80, "north": -6.80, "west": 110.99, "east": 114.55},
            "西爪哇省": {"south": -7.83, "north": -5.87, "west": 106.37, "east": 108.80},
            "日惹特区": {"south": -8.20, "north": -7.55, "west": 110.07, "east": 110.80},
        }
    },
    "俄罗斯": {
        "bbox": {"south": 41.19, "north": 81.85, "west": 19.64, "east": 169.05},
        "provinces": {
            "莫斯科": {"south": 55.47, "north": 55.97, "west": 37.14, "east": 37.97},
            "圣彼得堡": {"south": 59.72, "north": 60.18, "west": 29.82, "east": 30.67},
            "莫斯科州": {"south": 54.25, "north": 56.96, "west": 35.15, "east": 40.20},
            "克拉斯诺达尔边疆区": {"south": 43.40, "north": 46.80, "west": 36.56, "east": 41.78},
            "滨海边疆区": {"south": 42.28, "north": 48.45, "west": 130.40, "east": 139.20},
        }
    },
    "阿联酋": {
        "bbox": {"south": 22.63, "north": 26.08, "west": 51.58, "east": 56.38},
        "provinces": {
            "迪拜": {"south": 24.83, "north": 25.38, "west": 54.89, "east": 55.69},
            "阿布扎比": {"south": 22.63, "north": 25.00, "west": 51.58, "east": 55.94},
            "沙迦": {"south": 24.94, "north": 25.46, "west": 55.41, "east": 56.05},
        }
    },
    "马来西亚": {
        "bbox": {"south": 0.85, "north": 7.36, "west": 99.64, "east": 119.27},
        "provinces": {
            "吉隆坡": {"south": 3.04, "north": 3.24, "west": 101.60, "east": 101.77},
            "雪兰莪": {"south": 2.69, "north": 3.81, "west": 100.79, "east": 101.95},
            "槟城": {"south": 5.17, "north": 5.60, "west": 100.17, "east": 100.53},
            "柔佛": {"south": 1.26, "north": 2.72, "west": 102.48, "east": 104.28},
            "沙巴": {"south": 4.11, "north": 7.36, "west": 115.35, "east": 119.27},
            "砂拉越": {"south": 0.85, "north": 4.99, "west": 109.62, "east": 115.75},
        }
    },
    "菲律宾": {
        "bbox": {"south": 4.64, "north": 21.12, "west": 116.93, "east": 126.60},
        "provinces": {
            "马尼拉大都会": {"south": 14.37, "north": 14.76, "west": 120.92, "east": 121.17},
            "宿务": {"south": 9.97, "north": 11.20, "west": 123.48, "east": 124.15},
            "达沃": {"south": 6.73, "north": 7.63, "west": 125.28, "east": 125.77},
            "碧瑶": {"south": 16.31, "north": 16.48, "west": 120.48, "east": 120.69},
        }
    },
    "新加坡": {
        "bbox": {"south": 1.16, "north": 1.47, "west": 103.60, "east": 104.07},
        "provinces": {
            "新加坡全境": {"south": 1.16, "north": 1.47, "west": 103.60, "east": 104.07},
        }
    },
    "沙特阿拉伯": {
        "bbox": {"south": 16.38, "north": 32.16, "west": 34.49, "east": 55.64},
        "provinces": {
            "利雅得": {"south": 24.28, "north": 25.21, "west": 46.29, "east": 47.06},
            "麦加": {"south": 21.08, "north": 21.68, "west": 39.55, "east": 40.17},
            "麦地那": {"south": 24.21, "north": 24.70, "west": 39.31, "east": 39.85},
            "东部省": {"south": 25.36, "north": 26.78, "west": 49.54, "east": 50.20},
        }
    },
    "土耳其": {
        "bbox": {"south": 35.81, "north": 42.11, "west": 25.62, "east": 44.82},
        "provinces": {
            "伊斯坦布尔": {"south": 40.87, "north": 41.42, "west": 28.54, "east": 29.38},
            "安卡拉": {"south": 39.57, "north": 40.25, "west": 32.39, "east": 33.16},
            "安塔利亚": {"south": 36.65, "north": 37.09, "west": 30.48, "east": 30.92},
            "伊兹密尔": {"south": 38.19, "north": 38.60, "west": 26.93, "east": 27.37},
        }
    },
    "墨西哥": {
        "bbox": {"south": 14.53, "north": 32.72, "west": -118.45, "east": -86.71},
        "provinces": {
            "墨西哥城": {"south": 19.18, "north": 19.59, "west": -99.33, "east": -98.95},
            "金塔纳罗奥州": {"south": 18.50, "north": 21.62, "west": -88.97, "east": -86.71},
            "哈利斯科州": {"south": 19.00, "north": 22.75, "west": -105.69, "east": -101.82},
            "新莱昂州": {"south": 23.16, "north": 27.81, "west": -101.23, "east": -98.39},
        }
    },
    "阿根廷": {
        "bbox": {"south": -55.06, "north": -21.78, "west": -73.57, "east": -53.64},
        "provinces": {
            "布宜诺斯艾利斯": {"south": -34.87, "north": -34.43, "west": -58.68, "east": -58.25},
            "布宜诺斯艾利斯省": {"south": -41.03, "north": -33.26, "west": -63.39, "east": -56.67},
            "科尔多瓦省": {"south": -35.00, "north": -29.50, "west": -65.77, "east": -61.78},
            "圣克鲁斯省": {"south": -52.38, "north": -46.00, "west": -73.57, "east": -65.90},
        }
    },
    "南非": {
        "bbox": {"south": -34.84, "north": -22.13, "west": 16.45, "east": 32.90},
        "provinces": {
            "豪登省": {"south": -26.92, "north": -25.34, "west": 27.15, "east": 28.91},
            "西开普省": {"south": -34.84, "north": -30.42, "west": 17.78, "east": 24.21},
            "夸祖鲁-纳塔尔省": {"south": -31.25, "north": -26.80, "west": 28.86, "east": 32.90},
        }
    },
    "埃及": {
        "bbox": {"south": 22.00, "north": 31.67, "west": 24.70, "east": 36.90},
        "provinces": {
            "开罗": {"south": 29.83, "north": 30.20, "west": 31.08, "east": 31.54},
            "亚历山大": {"south": 31.07, "north": 31.39, "west": 29.70, "east": 30.05},
            "卢克索": {"south": 25.48, "north": 25.77, "west": 32.49, "east": 32.77},
            "南西奈省": {"south": 27.72, "north": 29.90, "west": 32.69, "east": 34.97},
        }
    },
    "新西兰": {
        "bbox": {"south": -47.29, "north": -34.39, "west": 166.43, "east": 178.58},
        "provinces": {
            "奥克兰": {"south": -37.01, "north": -36.38, "west": 174.44, "east": 175.10},
            "惠灵顿": {"south": -41.44, "north": -41.17, "west": 174.66, "east": 174.92},
            "坎特伯雷": {"south": -44.95, "north": -42.39, "west": 169.92, "east": 173.70},
            "皇后镇": {"south": -45.12, "north": -44.94, "west": 168.57, "east": 168.82},
        }
    },
    "荷兰": {
        "bbox": {"south": 50.75, "north": 53.47, "west": 3.37, "east": 7.22},
        "provinces": {
            "北荷兰省": {"south": 52.20, "north": 53.47, "west": 4.49, "east": 5.26},
            "南荷兰省": {"south": 51.69, "north": 52.32, "west": 3.84, "east": 4.96},
            "北布拉班特省": {"south": 51.27, "north": 51.82, "west": 4.10, "east": 5.94},
        }
    },
    "瑞士": {
        "bbox": {"south": 45.82, "north": 47.81, "west": 5.96, "east": 10.49},
        "provinces": {
            "苏黎世州": {"south": 47.14, "north": 47.66, "west": 8.33, "east": 8.82},
            "日内瓦州": {"south": 46.13, "north": 46.30, "west": 5.96, "east": 6.27},
            "伯尔尼州": {"south": 46.28, "north": 47.24, "west": 6.87, "east": 8.47},
            "沃州": {"south": 46.14, "north": 46.94, "west": 6.09, "east": 7.21},
        }
    },
    "瑞典": {
        "bbox": {"south": 55.34, "north": 69.06, "west": 10.96, "east": 24.17},
        "provinces": {
            "斯德哥尔摩省": {"south": 58.75, "north": 60.22, "west": 17.14, "east": 19.30},
            "西约塔兰省": {"south": 57.10, "north": 59.05, "west": 11.10, "east": 14.62},
            "斯科讷省": {"south": 55.34, "north": 56.52, "west": 12.57, "east": 14.62},
        }
    },
    "葡萄牙": {
        "bbox": {"south": 36.96, "north": 42.15, "west": -9.50, "east": -6.19},
        "provinces": {
            "里斯本": {"south": 38.62, "north": 38.86, "west": -9.28, "east": -9.00},
            "波尔图": {"south": 41.06, "north": 41.24, "west": -8.71, "east": -8.51},
            "法鲁区": {"south": 36.96, "north": 37.53, "west": -9.01, "east": -7.40},
        }
    },
    "波兰": {
        "bbox": {"south": 49.00, "north": 54.84, "west": 14.12, "east": 24.15},
        "provinces": {
            "华沙": {"south": 52.07, "north": 52.37, "west": 20.85, "east": 21.27},
            "克拉科夫": {"south": 49.97, "north": 50.13, "west": 19.79, "east": 20.10},
            "马佐夫舍省": {"south": 51.00, "north": 53.49, "west": 19.96, "east": 23.18},
        }
    },
    "希腊": {
        "bbox": {"south": 34.80, "north": 41.75, "west": 19.37, "east": 29.65},
        "provinces": {
            "雅典": {"south": 37.85, "north": 38.12, "west": 23.60, "east": 23.87},
            "塞萨洛尼基": {"south": 40.51, "north": 40.71, "west": 22.85, "east": 23.04},
            "克里特岛": {"south": 34.80, "north": 35.70, "west": 23.51, "east": 26.33},
        }
    },
    "比利时": {
        "bbox": {"south": 49.50, "north": 51.50, "west": 2.55, "east": 6.40},
        "provinces": {
            "布鲁塞尔": {"south": 50.77, "north": 50.92, "west": 4.26, "east": 4.48},
            "安特卫普": {"south": 51.14, "north": 51.42, "west": 4.19, "east": 4.55},
            "东佛兰德省": {"south": 50.69, "north": 51.24, "west": 3.33, "east": 4.08},
        }
    },
    "奥地利": {
        "bbox": {"south": 46.37, "north": 49.02, "west": 9.53, "east": 17.16},
        "provinces": {
            "维也纳": {"south": 48.10, "north": 48.32, "west": 16.18, "east": 16.58},
            "蒂罗尔州": {"south": 46.65, "north": 47.75, "west": 10.10, "east": 12.98},
            "萨尔茨堡州": {"south": 46.95, "north": 48.05, "west": 12.08, "east": 13.90},
        }
    },
}

# 数据类别定义
CATEGORIES = {
    "highway": {
        "name": "交通路线 (线要素)",
        "geom": "line",
        "table_prefix": "osm_highway",
        "desc": "道路网 — 高速、国道、省道、街道等",
    },
    "building": {
        "name": "建筑轮廓 (面要素)",
        "geom": "polygon",
        "table_prefix": "osm_building",
        "desc": "建筑物外轮廓",
    },
    "natural": {
        "name": "自然地貌 (面要素)",
        "geom": "polygon",
        "table_prefix": "osm_natural",
        "desc": "水域、林地、草地、湿地等",
    },
    "landuse": {
        "name": "土地利用 (面要素)",
        "geom": "polygon",
        "table_prefix": "osm_landuse",
        "desc": "居住区、商业区、工业区、农田等",
    },
}

# 线要素表字段 (way/relation id 在不同命名空间，需联合主键)
LINE_TABLE_COLS = (
    "osm_id BIGINT NOT NULL, "
    "osm_type TEXT NOT NULL DEFAULT 'way', "
    "name TEXT, "
    "sub_type TEXT, "
    "geom JSONB, "
    "tags JSONB, "
    "batch_id TEXT, "
    "PRIMARY KEY (osm_id, osm_type)"
)

# 面要素表字段
POLYGON_TABLE_COLS = (
    "osm_id BIGINT NOT NULL, "
    "osm_type TEXT NOT NULL DEFAULT 'way', "
    "name TEXT, "
    "sub_type TEXT, "
    "geom JSONB, "
    "tags JSONB, "
    "batch_id TEXT, "
    "PRIMARY KEY (osm_id, osm_type)"
)

LINE_SHP_FIELDS = [
    ("osm_id", "N", 20, 0),
    ("osm_type", "C", 10, 0),
    ("name", "C", 200, 0),
    ("sub_type", "C", 50, 0),
]

POLYGON_SHP_FIELDS = [
    ("osm_id", "N", 20, 0),
    ("osm_type", "C", 10, 0),
    ("name", "C", 200, 0),
    ("sub_type", "C", 50, 0),
]

# WGS84 PRJ 文件内容
PRJ_WGS84 = (
    'GEOGCS["WGS 84",DATUM["WGS_1984",SPHEROID["WGS 84",6378137,298.257223563]],'
    'PRIMEM["Greenwich",0],UNIT["degree",0.0174532925199433]]'
)

DEFAULT_CONFIG = {
    "db_host": "localhost",
    "db_port": 5432,
    "db_user": "postgres",
    "db_password": "",
    "db_name": "osm_data",
    "area_name": "",
    "tile_size": 1.0,
}

# ============================================================
# 工具函数 — Overpass 几何 → WKT / 坐标
# ============================================================

def overpass_geom_to_coords(geom, geom_type="line"):
    """
    把 Overpass JSON 几何转为 pyshp 可用的坐标列表。
    返回 list of rings, each ring is list of [lon, lat]
    """
    if not geom:
        return []
    if isinstance(geom[0], dict):
        # 单环: [{lat, lon}, ...]
        ring = [[p["lon"], p["lat"]] for p in geom]
        return [ring]
    elif isinstance(geom[0], list):
        # 多环 (multipolygon / 含洞多边形)
        rings = []
        for ring in geom:
            if ring and isinstance(ring[0], dict):
                rings.append([[p["lon"], p["lat"]] for p in ring])
        return rings
    return []


def overpass_geom_to_wkt(geom, geom_type="line"):
    """Overpass JSON 几何 → WKT 字符串"""
    rings = overpass_geom_to_coords(geom, geom_type)
    if not rings:
        return None

    def _ring_wkt(ring):
        return "(" + ", ".join(f"{lon} {lat}" for lon, lat in ring) + ")"

    if geom_type == "line":
        if len(rings) == 1:
            coords = ", ".join(f"{lon} {lat}" for lon, lat in rings[0])
            return f"LINESTRING({coords})"
        else:
            rings_str = ", ".join(_ring_wkt(r) for r in rings)
            return f"MULTILINESTRING({rings_str})"
    else:
        if len(rings) == 1:
            return f"POLYGON({_ring_wkt(rings[0])})"
        else:
            rings_str = ", ".join(_ring_wkt(r) for r in rings)
            return f"MULTIPOLYGON({rings_str})"

# ============================================================
# Nominatim 地理编码
# ============================================================

def lookup_place(name):
    """
    查地名 → bbox。
    1) 先查内置中国省份表 (即时)
    2) 再查国外国家/地区表 (即时)
    3) 不在表中则用 Overpass 搜索 admin 边界 (后台线程调用)
    返回: {south, north, west, east, display_name} 或 None
    """
    clean = name.strip()

    # 精确/模糊匹配中国省份
    for prov_name, bbox in CN_PROVINCES.items():
        clean_prov = clean.rstrip("省市自治区")
        if clean_prov == prov_name or clean_prov == prov_name.rstrip("省市自治区"):
            return {
                "south": bbox["south"], "north": bbox["north"],
                "west": bbox["west"], "east": bbox["east"],
                "display_name": prov_name + " (内置省份数据)",
            }
    for prov_name, bbox in CN_PROVINCES.items():
        if prov_name in clean or clean in prov_name:
            return {
                "south": bbox["south"], "north": bbox["north"],
                "west": bbox["west"], "east": bbox["east"],
                "display_name": prov_name + " (内置省份数据)",
            }

    # 搜索国外国家
    for country_name, region in WORLD_REGIONS.items():
        if country_name in clean or clean in country_name:
            bbox = region["bbox"]
            return {
                "south": bbox["south"], "north": bbox["north"],
                "west": bbox["west"], "east": bbox["east"],
                "display_name": f"{country_name} (内置国家数据)",
            }

    # 搜索国外省/州
    for country_name, region in WORLD_REGIONS.items():
        for prov_name, prov_bbox in region.get("provinces", {}).items():
            if prov_name in clean or clean in prov_name:
                return {
                    "south": prov_bbox["south"], "north": prov_bbox["north"],
                    "west": prov_bbox["west"], "east": prov_bbox["east"],
                    "display_name": f"{country_name} → {prov_name} (内置数据)",
                }

    return None


def search_place_overpass(name):
    """用 Overpass API 搜索地名 (城市/区县), 在后台线程调用"""
    # 去除常见后缀尝试多种匹配
    variants = [name]
    for sfx in ["市", "县", "区", "镇", "乡"]:
        if name.endswith(sfx):
            variants.insert(0, name[: -len(sfx)])
    seen = set()
    for v in variants:
        if v in seen:
            continue
        seen.add(v)
        query = (
            f'[out:json][timeout:30];'
            f'rel["name"="{v}"]["boundary"="administrative"];'
            f'out bb 1;'
        )
        try:
            resp = _overpass_post(query, timeout=40)
            data = json.loads(resp.content)
            elements = data.get("elements", [])
            if not elements:
                continue
            bounds = elements[0].get("bounds", {})
            if bounds and bounds.get("minlat"):
                tags = elements[0].get("tags", {})
                display = tags.get("name:zh", tags.get("name", name))
                return {
                    "south": bounds["minlat"],
                    "north": bounds["maxlat"],
                    "west": bounds["minlon"],
                    "east": bounds["maxlon"],
                    "display_name": f"{display} (OSM边界)",
                }
        except Exception:
            continue
    return None


def split_bbox(bbox, tile_size=1.0):
    """把 bbox 切成 tile_size° × tile_size° 的瓦片"""
    tiles = []
    lat = bbox["south"]
    while lat < bbox["north"]:
        lat_next = min(lat + tile_size, bbox["north"])
        lon = bbox["west"]
        while lon < bbox["east"]:
            lon_next = min(lon + tile_size, bbox["east"])
            tiles.append({
                "south": round(lat, 6),
                "west": round(lon, 6),
                "north": round(lat_next, 6),
                "east": round(lon_next, 6),
            })
            lon = lon_next
        lat = lat_next
    return tiles

# ============================================================
# Overpass QL 构建 & 查询
# ============================================================

def build_overpass_query(category, bbox, timeout=180):
    """为指定类别和 bbox 构建 Overpass QL 查询"""
    s, w, n, e = bbox["south"], bbox["west"], bbox["north"], bbox["east"]

    if category == "highway":
        return (
            f'[out:json][timeout:{timeout}];'
            f'(way["highway"]({s},{w},{n},{e}););'
            f'out geom;'
        )
    elif category == "building":
        return (
            f'[out:json][timeout:{timeout}];'
            f'(way["building"]({s},{w},{n},{e});'
            f'relation["building"]({s},{w},{n},{e}););'
            f'out geom;'
        )
    elif category == "natural":
        # 只下载面状自然地貌，排除点状（peak, hill 等）
        return (
            f'[out:json][timeout:{timeout}];'
            f'(way["natural"~"^(water|wood|forest|wetland|grassland|scrub|heath|beach|'
            f'bare_rock|scree|shingle|sand|mud|glacier|bay|reef|stone)$"]'
            f'({s},{w},{n},{e});'
            f'relation["natural"~"^(water|wood|forest|wetland|grassland|scrub|heath|beach|'
            f'bare_rock|scree|shingle|sand|mud|glacier|bay|reef|stone)$"]'
            f'({s},{w},{n},{e}););'
            f'out geom;'
        )
    elif category == "landuse":
        return (
            f'[out:json][timeout:{timeout}];'
            f'(way["landuse"]({s},{w},{n},{e});'
            f'relation["landuse"]({s},{w},{n},{e}););'
            f'out geom;'
        )
    return ""


def _overpass_post(query, timeout=210):
    """发送 Overpass POST 请求 (bytes body, 避免 UA 拦截和中文编码问题)"""
    body = b"data=" + query.encode("utf-8")
    return requests.post(
        OVERPASS_URL,
        data=body,
        headers={
            "User-Agent": USER_AGENT,
            "Content-Type": "application/x-www-form-urlencoded",
        },
        timeout=timeout,
    )


def query_overpass(query, retries=3):
    """发送 Overpass 查询，带重试"""
    last_err = None
    for attempt in range(retries):
        try:
            resp = _overpass_post(query)
            if resp.status_code == 429:
                time.sleep(min(30, 2 ** attempt * 5))
                continue
            if resp.status_code == 504:
                last_err = Exception("服务器超时 (504)，尝试缩小区域")
                time.sleep(5)
                continue
            resp.raise_for_status()
            return json.loads(resp.content)
        except requests.RequestException as e:
            last_err = e
            time.sleep(2)
    raise last_err or Exception("Overpass 查询失败")


def parse_overpass_response(data, category):
    """
    解析 Overpass 响应，提取几何要素。
    返回 list of dict: {osm_id, osm_type, name, sub_type, geom_json, tags, osm_timestamp}
    """
    elements = data.get("elements", [])
    results = []
    tag_key = CATEGORIES[category].get("osm_tag_override") or category

    for el in elements:
        if "geometry" not in el or not el["geometry"]:
            continue
        tags = el.get("tags", {})
        name = tags.get("name", "") or tags.get("name:zh", "") or ""
        sub_type = tags.get(tag_key, "")

        results.append({
            "osm_id": el["id"],
            "osm_type": el["type"],
            "name": name,
            "sub_type": sub_type,
            "geom_json": el["geometry"],
            "tags": tags,
            "osm_timestamp": el.get("timestamp", ""),
        })

    return results

# ============================================================
# ConfigManager
# ============================================================

class ConfigManager:
    def __init__(self):
        self.config_path = os.path.join(_get_app_dir(), "osm_config.json")
        self.config = dict(DEFAULT_CONFIG)
        self.load()

    def load(self):
        try:
            with open(self.config_path, encoding="utf-8") as f:
                loaded = json.load(f)
                self.config.update(loaded)
        except (FileNotFoundError, json.JSONDecodeError, UnicodeDecodeError):
            try:
                os.remove(self.config_path)
            except OSError:
                pass

    def save(self):
        with open(self.config_path, "w", encoding="utf-8") as f:
            json.dump(self.config, f, ensure_ascii=False, indent=2)

    def get(self, key, default=None):
        return self.config.get(key, default)

# ============================================================
# DownloadEngine (后台线程)
# ============================================================

class DownloadEngine(threading.Thread):
    def __init__(self, config, bbox, categories, batch_id,
                 log_queue, progress_queue, stop_event):
        super().__init__(daemon=True)
        self.config = config
        self.bbox = bbox
        self.categories = categories
        self.batch_id = batch_id
        self.log_queue = log_queue
        self.progress_queue = progress_queue
        self.stop_event = stop_event

    def _log(self, msg):
        self.log_queue.put(("log", msg))

    def _progress(self, current, total, detail=""):
        self.progress_queue.put((current, total, detail))

    def run(self):
        try:
            self._do_run()
        except Exception as e:
            self._log(f"严重错误: {e}\n{traceback.format_exc()}")
            self.log_queue.put(("error", str(e)))

    def _ensure_table(self, conn, table_name, is_line):
        cols = LINE_TABLE_COLS if is_line else POLYGON_TABLE_COLS
        sql = f'CREATE TABLE IF NOT EXISTS "{table_name}" ({cols})'
        with conn.cursor() as cur:
            cur.execute(sql)
        conn.commit()

    def _do_run(self):
        cfg = self.config
        tile_size = float(cfg.get("tile_size", 1.0))
        tiles = split_bbox(self.bbox, tile_size)
        total_tiles = len(tiles) * len(self.categories)
        self._log(f"区域: [{self.bbox['south']:.3f}, {self.bbox['west']:.3f}] → "
                  f"[{self.bbox['north']:.3f}, {self.bbox['east']:.3f}]")
        self._log(f"瓦片大小: {tile_size}° × {tile_size}°, 共 {len(tiles)} 个瓦片")
        self._log(f"数据类别: {', '.join(CATEGORIES[c]['name'] for c in self.categories)}")
        self._log(f"总任务数: {total_tiles}")
        self._log("正在连接数据库...")

        try:
            conn = psycopg2.connect(
                host=cfg["db_host"],
                port=cfg["db_port"],
                user=cfg["db_user"],
                password=cfg["db_password"],
                dbname=cfg["db_name"],
                client_encoding="UTF8",
            )
        except Exception as e:
            self._log(f"数据库连接失败: {e}")
            self.log_queue.put(("error", str(e)))
            return

        area_slug = cfg.get("area_name", "unnamed").strip()
        stats = {}  # {category: {"new": N, "dup": N}}

        try:
            completed = 0
            for cat in self.categories:
                cat_info = CATEGORIES[cat]
                is_line = (cat_info["geom"] == "line")
                table_name = (
                    f"{cat_info['table_prefix']}_{area_slug}_{self.batch_id}"
                )

                self._log(f"\n{'='*50}")
                self._log(f"开始下载: {cat_info['name']}")
                self._log(f"数据表: {table_name}")

                self._ensure_table(conn, table_name, is_line)
                insert_sql = (
                    f'INSERT INTO "{table_name}" (osm_id, osm_type, name, sub_type, geom, tags, batch_id) '
                    f'VALUES (%(osm_id)s, %(osm_type)s, %(name)s, %(sub_type)s, %(geom)s, %(tags)s, %(batch_id)s)'
                )
                # PG 9.4 兼容: 先查后插，避免 duplicate key error

                new_count = 0
                dup_count = 0

                for ti, tile in enumerate(tiles):
                    if self.stop_event.is_set():
                        self._log("用户中止")
                        conn.close()
                        return

                    completed += 1
                    self._progress(completed, total_tiles,
                                   f"{cat_info['name']} 瓦片 {ti+1}/{len(tiles)}")

                    query = build_overpass_query(cat, tile)
                    try:
                        data = query_overpass(query)
                        elements = parse_overpass_response(data, cat)
                    except Exception as e:
                        self._log(f"  [警告] 瓦片 {ti+1}/{len(tiles)} 查询失败: {e}")
                        continue

                    tile_new = 0
                    tile_dup = 0
                    with conn.cursor() as cur:
                        for el in elements:
                            params = {
                                "osm_id": el["osm_id"],
                                "osm_type": el["osm_type"],
                                "name": el["name"],
                                "sub_type": el["sub_type"],
                                "geom": json.dumps(el["geom_json"], ensure_ascii=False),
                                "tags": json.dumps(el["tags"], ensure_ascii=False),
                                "batch_id": self.batch_id,
                            }
                            # PG 9.4 无 ON CONFLICT, 先 SELECT 去重
                            cur.execute(
                                f'SELECT 1 FROM "{table_name}" '
                                f'WHERE osm_id = %(osm_id)s AND osm_type = %(osm_type)s',
                                {"osm_id": el["osm_id"], "osm_type": el["osm_type"]})
                            if cur.fetchone():
                                tile_dup += 1
                                continue
                            try:
                                cur.execute(insert_sql, params)
                                tile_new += 1
                            except Exception as e:
                                self._log(f"    [警告] 插入失败 id={el['osm_id']}: {e}")
                                tile_dup += 1
                    conn.commit()

                    new_count += tile_new
                    dup_count += tile_dup
                    self._log(f"  [{ti+1}/{len(tiles)}] "
                              f"({tile['south']:.3f},{tile['west']:.3f})→"
                              f"({tile['north']:.3f},{tile['east']:.3f}) "
                              f"获取 {len(elements)} 要素, 新增 {tile_new}, "
                              f"重复 {tile_dup}")

                    time.sleep(0.8)  # 对 Overpass 服务器友好

                stats[cat] = {"new": new_count, "dup": dup_count}
                self._log(f"完成: {cat_info['name']} — 新增 {new_count} 条, "
                          f"重复 {dup_count} 条")

            # 汇总
            self._log(f"\n{'='*50}")
            self._log("全部下载完成!")
            for cat in self.categories:
                s = stats.get(cat, {"new": 0, "dup": 0})
                self._log(f"  {CATEGORIES[cat]['name']}: 新增 {s['new']} 条")
            self.log_queue.put(("done", stats))

        except Exception as e:
            self._log(f"下载过程异常: {e}\n{traceback.format_exc()}")
            self.log_queue.put(("error", str(e)))
        finally:
            conn.close()

# ============================================================
# App
# ============================================================

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("OSM 开放地图数据下载工具")
        self.geometry("1050x750")
        self.minsize(900, 650)

        self.config_mgr = ConfigManager()
        self.stop_event = threading.Event()
        self.engine = None
        self.log_queue = queue.Queue()
        self.progress_queue = queue.Queue()
        self.current_batch_id = None
        self.current_bbox = None
        self.category_vars = {}  # {cat_key: tk.BooleanVar}
        self.region_mode = "cn"  # "cn" | "world"
        self.world_country_var = None
        self.world_province_var = None

        self._apply_styles()
        self._build_ui()
        self._load_config_to_ui()
        self._poll_queues()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ============================================================
    # 样式
    # ============================================================

    def _apply_styles(self):
        style = ttk.Style()
        BG = "#F8F6FF"
        SURFACE = "#FFFFFF"
        TEXT = "#1E1B4B"
        TEXT_SEC = "#6D63B8"
        ACCENT = "#7C3AED"

        self.configure(bg="#0A0A1A")

        style.configure(".", font=("Microsoft YaHei UI", 9))
        style.configure("TFrame", background=BG)
        style.configure("TLabelframe", background=SURFACE)
        style.configure("TLabelframe.Label", background=SURFACE, foreground=TEXT,
                         font=("Microsoft YaHei UI", 10, "bold"))
        style.configure("TNotebook", background=BG, borderwidth=0)
        style.configure("TNotebook.Tab", padding=(18, 8),
                         font=("Microsoft YaHei UI", 10),
                         background="#F1EEFC", foreground=TEXT_SEC)
        style.map("TNotebook.Tab",
                  background=[("selected", SURFACE)],
                  foreground=[("selected", ACCENT)])
        style.configure("TLabel", background=BG, foreground=TEXT)
        style.configure("TEntry", padding=6, fieldbackground="#FAFAFE")
        style.configure("TButton", padding=(14, 6), font=("Microsoft YaHei UI", 9))
        style.configure("TCheckbutton", background=BG, foreground=TEXT)
        style.configure("TProgressbar", thickness=14,
                         troughcolor="#E8E4F8", background="#7C3AED")

    # ============================================================
    # UI 构建
    # ============================================================

    def _build_ui(self):
        # ── 顶部标题栏 ──
        header = tk.Frame(self, bg="#0A0A1A", height=48)
        header.pack(fill=tk.X)
        header.pack_propagate(False)

        title_frame = tk.Frame(header, bg="#0A0A1A")
        title_frame.pack(side=tk.LEFT, padx=15, pady=6)
        tk.Label(title_frame, text="◈", fg="#C084FC", bg="#0A0A1A",
                 font=("Microsoft YaHei UI", 14)).pack(side=tk.LEFT)
        tk.Label(title_frame, text=" OSM 开放地图数据下载工具 ",
                 bg="#0A0A1A", fg="#E9D5FF",
                 font=("Microsoft YaHei UI", 13, "bold")).pack(side=tk.LEFT)
        tk.Label(title_frame, text="◈", fg="#C084FC", bg="#0A0A1A",
                 font=("Microsoft YaHei UI", 14)).pack(side=tk.LEFT)

        info_frame = tk.Frame(header, bg="#0A0A1A")
        info_frame.pack(side=tk.RIGHT, padx=15, pady=8)
        tk.Label(info_frame, text="v1.0", fg="#A78BFA", bg="#0A0A1A",
                 font=("Consolas", 9, "bold")).pack(side=tk.RIGHT, padx=(15, 0))
        tk.Label(info_frame, text="白栋博  bdb15896810691", fg="#6C3CE0",
                 bg="#0A0A1A", font=("Microsoft YaHei UI", 9)).pack(side=tk.RIGHT)

        # ── 主容器 ──
        main_frame = ttk.Frame(self, padding="8")
        main_frame.pack(fill=tk.BOTH, expand=True)

        pane = ttk.PanedWindow(main_frame, orient=tk.VERTICAL)
        pane.pack(fill=tk.BOTH, expand=True)

        top_section = ttk.Frame(pane, height=400)
        self.notebook = ttk.Notebook(top_section)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        self._build_db_tab()
        self._build_area_tab()
        self._build_download_tab()
        self._build_export_tab()

        manager = tk.Frame(main_frame, bg="#0A0A1A", height=22)
        manager.pack(fill=tk.X, side=tk.BOTTOM, before=main_frame.winfo_children()[0])
        tk.Label(manager, text="数据源: OpenStreetMap | Overpass API | Nominatim",
                 fg="#6C3CE0", bg="#0A0A1A",
                 font=("Microsoft YaHei UI", 7)).pack(side=tk.LEFT, padx=10)

        # ── 底部: 日志 + 进度 ──
        bottom_section = ttk.Frame(main_frame)
        pane.add(top_section, weight=3)
        pane.add(bottom_section, weight=1)

        self.progress_var = tk.IntVar()
        self.progress_bar = ttk.Progressbar(
            bottom_section, variable=self.progress_var,
            mode="determinate", maximum=100)
        self.progress_bar.pack(fill=tk.X, padx=5, pady=(5, 0))

        self.progress_label = tk.Label(
            bottom_section, text="就绪", bg="#1E293B", fg="#94A3B8",
            font=("Microsoft YaHei UI", 8), anchor="w")
        self.progress_label.pack(fill=tk.X, padx=5)

        log_frame = ttk.Frame(bottom_section)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=(2, 5))

        self.log_text = tk.Text(
            log_frame, height=8, bg="#1E293B", fg="#E2E8F0",
            font=("Consolas", 9), wrap=tk.WORD, state=tk.DISABLED,
            relief=tk.FLAT, borderwidth=0)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        log_scroll = ttk.Scrollbar(log_frame, command=self.log_text.yview)
        log_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.configure(yscrollcommand=log_scroll.set)

    # ============================================================
    # Tab 1: 数据库配置
    # ============================================================

    def _build_db_tab(self):
        tab = ttk.Frame(self.notebook, padding="15")
        self.notebook.add(tab, text="  数据库配置  ")

        frame = ttk.LabelFrame(tab, text="PostgreSQL 连接参数", padding="15")
        frame.pack(fill=tk.X)

        fields = [
            ("主机:", "db_host", "localhost"),
            ("端口:", "db_port", "5432"),
            ("用户:", "db_user", "postgres"),
            ("密码:", "db_password", ""),
            ("数据库:", "db_name", "osm_data"),
        ]

        self.db_entries = {}
        for i, (label, key, default) in enumerate(fields):
            lbl = tk.Label(frame, text=label, bg="#F8F6FF", fg="#1E1B4B",
                           font=("Microsoft YaHei UI", 10), width=8, anchor="e")
            lbl.grid(row=i, column=0, padx=(0, 8), pady=5, sticky="e")

            show = "*" if key == "db_password" else None
            entry = tk.Entry(frame, font=("Consolas", 10),
                             show=show, relief=tk.FLAT, bd=1,
                             highlightbackground="#E2E0F0",
                             highlightthickness=1)
            entry.insert(0, default)
            entry.grid(row=i, column=1, sticky="ew", pady=5, ipady=3)
            self.db_entries[key] = entry

        frame.columnconfigure(1, weight=1)

        btn_frame = tk.Frame(frame, bg="#F8F6FF")
        btn_frame.grid(row=len(fields), column=0, columnspan=2,
                       pady=(15, 5), sticky="e")

        tk.Button(btn_frame, text="测试连接", bg="#7C3AED", fg="white",
                  font=("Microsoft YaHei UI", 9, "bold"),
                  relief=tk.FLAT, padx=16, pady=5,
                  activebackground="#6D28D9", activeforeground="white",
                  cursor="hand2", command=self._on_test_db).pack(side=tk.LEFT, padx=5)

        self.db_status = tk.Label(frame, text="", bg="#F8F6FF", fg="#6D63B8",
                                   font=("Microsoft YaHei UI", 9))
        self.db_status.grid(row=len(fields)+1, column=0, columnspan=2, pady=(0, 5))

    # ============================================================
    # Tab 2: 区域选择
    # ============================================================

    def _build_area_tab(self):
        tab = ttk.Frame(self.notebook, padding="15")
        self.notebook.add(tab, text="  区域选择  ")

        # ── 快捷选择 ──
        quick_frame = ttk.LabelFrame(tab, text="快捷选择 (即时，无需联网)", padding="12")
        quick_frame.pack(fill=tk.X, pady=(0, 10))

        # 国内/国外切换按钮
        toggle_frame = tk.Frame(quick_frame, bg="#F8F6FF")
        toggle_frame.pack(fill=tk.X, pady=(0, 8))

        self.btn_cn = tk.Button(toggle_frame, text="国内",
                                bg="#7C3AED", fg="white",
                                font=("Microsoft YaHei UI", 10, "bold"),
                                relief=tk.FLAT, padx=18, pady=4,
                                activebackground="#6D28D9", activeforeground="white",
                                cursor="hand2",
                                command=lambda: self._on_region_switch("cn"))
        self.btn_cn.pack(side=tk.LEFT, padx=(0, 4))

        self.btn_world = tk.Button(toggle_frame, text="国外",
                                   bg="#E8E4F8", fg="#6D63B8",
                                   font=("Microsoft YaHei UI", 10, "bold"),
                                   relief=tk.FLAT, padx=18, pady=4,
                                   activebackground="#DDD6FE", activeforeground="#6D63B8",
                                   cursor="hand2",
                                   command=lambda: self._on_region_switch("world"))
        self.btn_world.pack(side=tk.LEFT)

        # 国内省份行
        row1 = tk.Frame(quick_frame, bg="#F8F6FF")

        tk.Label(row1, text="省份:", bg="#F8F6FF", fg="#1E1B4B",
                 font=("Microsoft YaHei UI", 10)).pack(side=tk.LEFT)

        self.province_var = tk.StringVar()
        province_names = ["请选择省份..."] + sorted(CN_PROVINCES.keys())
        self.province_combo = ttk.Combobox(
            row1, textvariable=self.province_var,
            values=province_names, state="readonly", width=18,
            font=("Microsoft YaHei UI", 10))
        self.province_combo.pack(side=tk.LEFT, padx=(8, 12))
        self.province_combo.current(0)
        self.province_combo.bind("<<ComboboxSelected>>", self._on_province_select)

        # 国外国家行 (初始隐藏)
        self.row_world = tk.Frame(quick_frame, bg="#F8F6FF")
        self.world_country_var = tk.StringVar()
        country_names = ["请选择国家..."] + sorted(WORLD_REGIONS.keys())
        self.world_country_combo = ttk.Combobox(
            self.row_world, textvariable=self.world_country_var,
            values=country_names, state="readonly", width=18,
            font=("Microsoft YaHei UI", 10))
        self.world_country_label = tk.Label(self.row_world, text="国家:",
                                            bg="#F8F6FF", fg="#1E1B4B",
                                            font=("Microsoft YaHei UI", 10))
        self.world_country_label.pack(side=tk.LEFT)
        self.world_country_combo.pack(side=tk.LEFT, padx=(8, 12))
        self.world_country_combo.current(0)
        self.world_country_combo.bind("<<ComboboxSelected>>", self._on_country_select)

        # 国外省/州行 (初始隐藏)
        self.row_world_prov = tk.Frame(quick_frame, bg="#F8F6FF")
        self.world_province_var = tk.StringVar()
        self.world_province_combo = ttk.Combobox(
            self.row_world_prov, textvariable=self.world_province_var,
            values=["请选择省份/州..."], state="readonly", width=22,
            font=("Microsoft YaHei UI", 10))
        self.world_province_label = tk.Label(self.row_world_prov, text="省/州:",
                                             bg="#F8F6FF", fg="#1E1B4B",
                                             font=("Microsoft YaHei UI", 10))
        self.world_province_label.pack(side=tk.LEFT)
        self.world_province_combo.pack(side=tk.LEFT, padx=(8, 12))
        self.world_province_combo.current(0)
        self.world_province_combo.bind("<<ComboboxSelected>>", self._on_foreign_province_select)

        # 城市搜索行 (独立，始终可见)
        row_search = tk.Frame(quick_frame, bg="#F8F6FF")

        tk.Label(row_search, text="或输入城市/区县:", bg="#F8F6FF", fg="#1E1B4B",
                 font=("Microsoft YaHei UI", 10)).pack(side=tk.LEFT)

        self.entry_place = tk.Entry(row_search, font=("Microsoft YaHei UI", 11),
                                     relief=tk.FLAT, bd=1,
                                     highlightbackground="#C4B5FD",
                                     highlightthickness=1, width=18)
        self.entry_place.pack(side=tk.LEFT, padx=(8, 8), ipady=3)
        self.entry_place.bind("<Return>", lambda e: self._on_geocode_async())

        self.btn_search = tk.Button(row_search, text="搜索", bg="#7C3AED", fg="white",
                                     font=("Microsoft YaHei UI", 10, "bold"),
                                     relief=tk.FLAT, padx=16, pady=4,
                                     activebackground="#6D28D9",
                                     activeforeground="white",
                                     cursor="hand2",
                                     command=self._on_geocode_async)
        self.btn_search.pack(side=tk.LEFT)

        # pack 顺序: 国内行(默认可见) → 搜索行(始终可见)
        # 国外行在切换时动态 pack_forget / pack
        row1.pack(fill=tk.X, pady=(0, 4))
        row_search.pack(fill=tk.X, pady=(0, 5))

        # 查询结果
        self.lbl_geocode_result = tk.Label(
            quick_frame,
            text="选择省份或输入城市名称搜索 (Overpass API，约需3-10秒)",
            bg="#F8F6FF", fg="#6D63B8", font=("Microsoft YaHei UI", 9),
            wraplength=700, justify="left")
        self.lbl_geocode_result.pack(fill=tk.X, pady=(10, 0))

        # ── 边界框坐标 ──
        bbox_frame = ttk.LabelFrame(tab, text="边界框坐标 (WGS84)", padding="12")
        bbox_frame.pack(fill=tk.X, pady=(0, 10))

        coord_grid = tk.Frame(bbox_frame, bg="#F8F6FF")
        coord_grid.pack()

        self.bbox_entries = {}
        labels = [("南纬 (South)", "south"), ("北纬 (North)", "north"),
                   ("西经 (West)", "west"), ("东经 (East)", "east")]
        for i, (label, key) in enumerate(labels):
            col = i * 2
            tk.Label(coord_grid, text=label + ":", bg="#F8F6FF", fg="#1E1B4B",
                     font=("Microsoft YaHei UI", 9)).grid(row=0, column=col,
                                                           padx=(10 if col>0 else 0, 4),
                                                           pady=5)
            entry = tk.Entry(coord_grid, font=("Consolas", 10), width=10,
                             relief=tk.FLAT, bd=1,
                             highlightbackground="#E2E0F0", highlightthickness=1)
            entry.grid(row=0, column=col+1, padx=(0, 5), pady=5, ipady=2)
            self.bbox_entries[key] = entry

        # 瓦片设置
        tile_frame = tk.Frame(bbox_frame, bg="#F8F6FF")
        tile_frame.pack(fill=tk.X, pady=(10, 0))

        tk.Label(tile_frame, text="瓦片大小:", bg="#F8F6FF", fg="#1E1B4B",
                 font=("Microsoft YaHei UI", 9)).pack(side=tk.LEFT)

        self.tile_size_var = tk.StringVar(value="1.0")
        tile_combo = ttk.Combobox(tile_frame, textvariable=self.tile_size_var,
                                   values=["0.25", "0.5", "1.0", "2.0"],
                                   state="readonly", width=6,
                                   font=("Consolas", 10))
        tile_combo.pack(side=tk.LEFT, padx=(8, 8))
        tile_combo.bind("<<ComboboxSelected>>", lambda e: self._update_tile_info())

        tk.Label(tile_frame, text="° (区域越大建议用越大瓦片)", bg="#F8F6FF",
                 fg="#6D63B8", font=("Microsoft YaHei UI", 8)).pack(side=tk.LEFT)

        self.lbl_tile_info = tk.Label(
            tile_frame, text="", bg="#F8F6FF", fg="#7C3AED",
            font=("Microsoft YaHei UI", 9, "bold"))
        self.lbl_tile_info.pack(side=tk.RIGHT)

    # ============================================================
    # Tab 3: 数据下载
    # ============================================================

    def _build_download_tab(self):
        tab = ttk.Frame(self.notebook, padding="15")
        self.notebook.add(tab, text="  数据下载  ")

        # ── 类别选择 ──
        cat_frame = ttk.LabelFrame(tab, text="数据类别", padding="12")
        cat_frame.pack(fill=tk.X, pady=(0, 10))

        self.category_vars = {}
        for cat_key, cat_info in CATEGORIES.items():
            var = tk.BooleanVar(value=True)
            self.category_vars[cat_key] = var

            row = tk.Frame(cat_frame, bg="#F8F6FF")
            row.pack(fill=tk.X, pady=2)

            cb = tk.Checkbutton(row, text=cat_info["name"],
                                variable=var, bg="#F8F6FF", fg="#1E1B4B",
                                font=("Microsoft YaHei UI", 10, "bold"),
                                activebackground="#F8F6FF",
                                selectcolor="#EDE9FE",
                                cursor="hand2")
            cb.pack(side=tk.LEFT)

            tk.Label(row, text=cat_info["desc"], bg="#F8F6FF", fg="#6D63B8",
                     font=("Microsoft YaHei UI", 8)).pack(side=tk.LEFT, padx=(10, 0))

        # ── 控制按钮 ──
        ctrl_frame = tk.Frame(tab, bg="#F8F6FF")
        ctrl_frame.pack(fill=tk.X, pady=(0, 10))

        self.btn_start = tk.Button(ctrl_frame, text="▶  开始爬取",
                                    bg="#7C3AED", fg="white",
                                    font=("Microsoft YaHei UI", 11, "bold"),
                                    relief=tk.FLAT, padx=24, pady=6,
                                    activebackground="#6D28D9",
                                    activeforeground="white",
                                    cursor="hand2", command=self._on_start)
        self.btn_start.pack(side=tk.LEFT, padx=(0, 8))

        self.btn_stop = tk.Button(ctrl_frame, text="■  中止",
                                   bg="#EF4444", fg="white",
                                   font=("Microsoft YaHei UI", 11, "bold"),
                                   relief=tk.FLAT, padx=24, pady=6,
                                   activebackground="#DC2626",
                                   activeforeground="white",
                                   cursor="hand2", command=self._on_stop,
                                   state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT)

        self.status_label = tk.Label(ctrl_frame, text="就绪", bg="#F8F6FF",
                                      fg="#6D63B8", font=("Microsoft YaHei UI", 9))
        self.status_label.pack(side=tk.RIGHT, padx=10)

    # ============================================================
    # Tab 4: SHP 导出
    # ============================================================

    def _build_export_tab(self):
        tab = ttk.Frame(self.notebook, padding="15")
        self.notebook.add(tab, text="  SHP 导出  ")

        exp_frame = ttk.LabelFrame(tab, text="导出 OSM 数据表为 Shapefile", padding="12")
        exp_frame.pack(fill=tk.BOTH, expand=True)

        hint = tk.Label(exp_frame, text="选择数据库中的 OSM 表，导出为 SHP + CSV + PRJ",
                        bg="#F8F6FF", fg="#6D63B8",
                        font=("Microsoft YaHei UI", 9))
        hint.pack(anchor="w", pady=(0, 8))

        list_frame = ttk.Frame(exp_frame)
        list_frame.pack(fill=tk.BOTH, expand=True)

        self.export_listbox = tk.Listbox(list_frame, font=("Consolas", 10),
                                          selectmode=tk.SINGLE,
                                          bg="#FAFAFE", fg="#1E1B4B",
                                          relief=tk.FLAT, bd=1,
                                          highlightbackground="#E2E0F0",
                                          highlightthickness=1)
        self.export_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        lb_scroll = ttk.Scrollbar(list_frame, command=self.export_listbox.yview)
        lb_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.export_listbox.configure(yscrollcommand=lb_scroll.set)

        btn_row = tk.Frame(exp_frame, bg="#F8F6FF")
        btn_row.pack(fill=tk.X, pady=(10, 0))

        tk.Button(btn_row, text="刷新表列表", bg="#6D63B8", fg="white",
                  font=("Microsoft YaHei UI", 9),
                  relief=tk.FLAT, padx=14, pady=4,
                  cursor="hand2", command=self._on_refresh_tables).pack(side=tk.LEFT)

        tk.Button(btn_row, text="导出选中表 → SHP", bg="#7C3AED", fg="white",
                  font=("Microsoft YaHei UI", 10, "bold"),
                  relief=tk.FLAT, padx=20, pady=5,
                  activebackground="#6D28D9", activeforeground="white",
                  cursor="hand2", command=self._on_export_shp).pack(side=tk.RIGHT)

    # ============================================================
    # 事件处理
    # ============================================================

    def _load_config_to_ui(self):
        cfg = self.config_mgr.config
        for key, entry in self.db_entries.items():
            val = cfg.get(key, "")
            entry.delete(0, tk.END)
            entry.insert(0, str(val))
        area = cfg.get("area_name", "")
        self.entry_place.delete(0, tk.END)
        self.entry_place.insert(0, area)
        bbox = cfg.get("bbox", {})
        for key in ("south", "west", "north", "east"):
            if key in self.bbox_entries:
                self.bbox_entries[key].delete(0, tk.END)
                self.bbox_entries[key].insert(0, str(bbox.get(key, "")))
        ts = cfg.get("tile_size", 1.0)
        self.tile_size_var.set(str(ts))

    def _get_config_from_ui(self):
        cfg = dict(self.config_mgr.config)
        for key, entry in self.db_entries.items():
            val = entry.get().strip()
            try:
                cfg[key] = int(val) if key == "db_port" else val
            except ValueError:
                cfg[key] = val
        cfg["area_name"] = self.entry_place.get().strip()
        cfg["tile_size"] = float(self.tile_size_var.get())
        bbox = {}
        for key in ("south", "west", "north", "east"):
            try:
                bbox[key] = float(self.bbox_entries[key].get().strip())
            except (ValueError, KeyError):
                bbox[key] = 0.0
        cfg["bbox"] = bbox
        return cfg

    def _get_bbox(self):
        bbox = {}
        for key in ("south", "west", "north", "east"):
            try:
                bbox[key] = float(self.bbox_entries[key].get().strip())
            except (ValueError, KeyError):
                return None
        if bbox["south"] >= bbox["north"] or bbox["west"] >= bbox["east"]:
            return None
        return bbox

    def _update_tile_info(self):
        bbox = self._get_bbox()
        if not bbox:
            self.lbl_tile_info.config(text="")
            return
        ts = float(self.tile_size_var.get())
        tiles = split_bbox(bbox, ts)
        lat_span = bbox["north"] - bbox["south"]
        lon_span = bbox["east"] - bbox["west"]
        self.lbl_tile_info.config(
            text=f"范围: {lat_span:.2f}° × {lon_span:.2f}° → 约 {len(tiles)} 个瓦片")

    def _on_test_db(self):
        try:
            cfg = self._get_config_from_ui()
            conn = psycopg2.connect(
                host=cfg["db_host"], port=cfg["db_port"],
                user=cfg["db_user"], password=cfg["db_password"],
                dbname=cfg["db_name"], client_encoding="UTF8",
            )
            conn.close()
            self.db_status.config(text="✓ 数据库连接成功", fg="#059669")
        except Exception as e:
            self.db_status.config(text=f"✗ 连接失败: {e}", fg="#EF4444")

    def _on_province_select(self, event=None):
        """省份下拉框选择 → 即时填入 bbox"""
        name = self.province_var.get()
        if not name or name.startswith("请选择"):
            return
        bbox = CN_PROVINCES.get(name)
        if not bbox:
            return
        for key in ("south", "north", "west", "east"):
            self.bbox_entries[key].delete(0, tk.END)
            self.bbox_entries[key].insert(0, str(bbox[key]))
        self.lbl_geocode_result.config(
            text=f"✓ {name} (内置数据)",
            fg="#059669")
        self.current_bbox = bbox
        self._update_tile_info()

    # ── 国内/国外切换 ──

    def _on_region_switch(self, mode):
        """切换国内/国外模式"""
        self.region_mode = mode
        if mode == "cn":
            self.btn_cn.config(bg="#7C3AED", fg="white")
            self.btn_world.config(bg="#E8E4F8", fg="#6D63B8")
            # 显示国内行，隐藏国外行
            self.row_world.pack_forget()
            self.row_world_prov.pack_forget()
            # 国内行需要重新 pack
            for child in self.province_combo.master.winfo_children():
                pass
            self.province_combo.master.pack(
                fill=tk.X, pady=(0, 4),
                before=self.entry_place.master)
        else:
            self.btn_world.config(bg="#7C3AED", fg="white")
            self.btn_cn.config(bg="#E8E4F8", fg="#6D63B8")
            # 隐藏国内行，显示国外行
            self.province_combo.master.pack_forget()
            self.row_world.pack(fill=tk.X, pady=(0, 4),
                                before=self.entry_place.master)
            self.row_world_prov.pack(fill=tk.X, pady=(0, 4),
                                     before=self.entry_place.master)

    def _on_country_select(self, event=None):
        """选择国外国家 → 填入国家级 bbox + 更新省/州下拉框"""
        name = self.world_country_var.get()
        if not name or name.startswith("请选择"):
            return
        region = WORLD_REGIONS.get(name)
        if not region:
            return

        # 填入国家级 bbox
        bbox = region["bbox"]
        for key in ("south", "north", "west", "east"):
            self.bbox_entries[key].delete(0, tk.END)
            self.bbox_entries[key].insert(0, str(bbox[key]))
        self.lbl_geocode_result.config(
            text=f"✓ {name} (国家级范围)\n"
                 f"  范围: [{bbox['south']:.4f}, {bbox['west']:.4f}] → "
                 f"[{bbox['north']:.4f}, {bbox['east']:.4f}]",
            fg="#059669")
        self.current_bbox = bbox
        self._update_tile_info()

        # 更新省/州下拉框
        provinces = region.get("provinces", {})
        prov_names = ["请选择省份/州..."] + sorted(provinces.keys())
        self.world_province_combo["values"] = prov_names
        self.world_province_combo.current(0)

    def _on_foreign_province_select(self, event=None):
        """选择国外省/州 → 填入省级 bbox"""
        country_name = self.world_country_var.get()
        prov_name = self.world_province_var.get()
        if (not country_name or country_name.startswith("请选择") or
                not prov_name or prov_name.startswith("请选择")):
            return
        region = WORLD_REGIONS.get(country_name)
        if not region:
            return
        prov = region.get("provinces", {}).get(prov_name)
        if not prov:
            return

        for key in ("south", "north", "west", "east"):
            self.bbox_entries[key].delete(0, tk.END)
            self.bbox_entries[key].insert(0, str(prov[key]))
        self.lbl_geocode_result.config(
            text=f"✓ {country_name} → {prov_name}\n"
                 f"  范围: [{prov['south']:.4f}, {prov['west']:.4f}] → "
                 f"[{prov['north']:.4f}, {prov['east']:.4f}]",
            fg="#059669")
        self.current_bbox = prov
        self._update_tile_info()

    def _on_geocode_async(self):
        """后台线程搜索地名"""
        name = self.entry_place.get().strip()
        if not name:
            # 如果输入为空但选了省份，不提示
            return

        # 先查内置表
        builtin = lookup_place(name)
        if builtin:
            for key in ("south", "north", "west", "east"):
                self.bbox_entries[key].delete(0, tk.END)
                self.bbox_entries[key].insert(0, str(builtin[key]))
            self.lbl_geocode_result.config(
                text=f"✓ {builtin['display_name']}\n"
                     f"  范围: [{builtin['south']:.4f}, {builtin['west']:.4f}] → "
                     f"[{builtin['north']:.4f}, {builtin['east']:.4f}]",
                fg="#059669")
            self.current_bbox = builtin
            self._update_tile_info()
            return

        # 内置表没命中 → 后台线程用 Overpass 搜索
        self.lbl_geocode_result.config(
            text=f"⏳ 正在搜索: {name} (Overpass API)...", fg="#7C3AED")
        self.btn_search.config(state=tk.DISABLED, text="搜索中...")

        def _search_thread():
            result = search_place_overpass(name)
            self.after(0, lambda: self._on_geocode_result(name, result))

        t = threading.Thread(target=_search_thread, daemon=True)
        t.start()

    def _on_geocode_result(self, name, result):
        """后台搜索完成回调 (主线程)"""
        self.btn_search.config(state=tk.NORMAL, text="搜索")
        if not result:
            self.lbl_geocode_result.config(
                text=f"✗ 未找到「{name}」，请尝试更具体的名称 (如: 郑州市, 浦东新区) "
                     f"或手动输入边界框坐标",
                fg="#EF4444")
            return

        for key in ("south", "north", "west", "east"):
            self.bbox_entries[key].delete(0, tk.END)
            self.bbox_entries[key].insert(0, str(round(result[key], 6)))

        self.lbl_geocode_result.config(
            text=f"✓ {result['display_name']}\n"
                 f"  范围: [{result['south']:.4f}, {result['west']:.4f}] → "
                 f"[{result['north']:.4f}, {result['east']:.4f}]",
            fg="#059669")
        self.current_bbox = result
        self._update_tile_info()

    def _on_start(self):
        # 保存配置
        cfg = self._get_config_from_ui()
        self.config_mgr.config = cfg
        self.config_mgr.save()

        bbox = self._get_bbox()
        if not bbox:
            messagebox.showwarning("提示", "请先在 [区域选择] 标签页查询地名或填写边界框坐标")
            return

        selected_cats = [k for k, v in self.category_vars.items() if v.get()]
        if not selected_cats:
            messagebox.showwarning("提示", "请至少选择一种数据类别")
            return

        # 测试数据库连接
        try:
            conn = psycopg2.connect(
                host=cfg["db_host"], port=cfg["db_port"],
                user=cfg["db_user"], password=cfg["db_password"],
                dbname=cfg["db_name"], client_encoding="UTF8",
            )
            conn.close()
        except Exception as e:
            messagebox.showerror("数据库错误", f"无法连接数据库:\n{e}")
            return

        self.current_batch_id = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.current_bbox = bbox

        self._clear_log()
        self._log(f"批次: {self.current_batch_id}")
        self._log(f"区域: [{bbox['south']:.3f}, {bbox['west']:.3f}] → "
                  f"[{bbox['north']:.3f}, {bbox['east']:.3f}]")
        self._log(f"瓦片: {self.tile_size_var.get()}° × {self.tile_size_var.get()}°")
        self._log(f"类别: {', '.join(CATEGORIES[c]['name'] for c in selected_cats)}")

        self.stop_event.clear()
        self.engine = DownloadEngine(
            config=cfg,
            bbox=bbox,
            categories=selected_cats,
            batch_id=self.current_batch_id,
            log_queue=self.log_queue,
            progress_queue=self.progress_queue,
            stop_event=self.stop_event,
        )

        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.progress_var.set(0)
        self.status_label.config(text="爬取中...", fg="#7C3AED")

        self.engine.start()

    def _on_stop(self):
        self.stop_event.set()
        self._log("正在中止...")
        self.btn_start.config(state=tk.NORMAL)
        self.btn_stop.config(state=tk.DISABLED)
        self.status_label.config(text="已中止", fg="#EF4444")

    def _on_refresh_tables(self):
        """刷新导出标签页的表列表"""
        cfg = self._get_config_from_ui()
        try:
            conn = psycopg2.connect(
                host=cfg["db_host"], port=cfg["db_port"],
                user=cfg["db_user"], password=cfg["db_password"],
                dbname=cfg["db_name"], client_encoding="UTF8",
            )
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT table_name
                    FROM information_schema.tables
                    WHERE table_schema='public' AND table_type='BASE TABLE'
                      AND table_name LIKE 'osm_%'
                    ORDER BY table_name DESC
                """)
                tables = [r[0] for r in cur.fetchall()]
            conn.close()
        except Exception as e:
            messagebox.showerror("错误", f"获取表列表失败:\n{e}")
            return

        self.export_listbox.delete(0, tk.END)
        if not tables:
            self.export_listbox.insert(tk.END, "  (暂无 OSM 数据表)")
        else:
            for t in tables:
                self.export_listbox.insert(tk.END, t)
            self.export_listbox.selection_set(0)

    def _on_export_shp(self):
        """导出选中表为 Shapefile"""
        sel = self.export_listbox.curselection()
        if not sel:
            messagebox.showwarning("提示", "请先选择要导出的数据表")
            return

        table = self.export_listbox.get(sel[0])
        if not table or table.startswith(" "):
            messagebox.showwarning("提示", "请先刷新表列表并选择有效的数据表")
            return

        cfg = self._get_config_from_ui()

        # 判断要素类型 (通过表名前缀)
        is_line = table.startswith("osm_highway")

        default_name = f"{table}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        shp_path = filedialog.asksaveasfilename(
            title=f"导出 {table} → Shapefile",
            defaultextension=".shp",
            filetypes=[("Shapefile", "*.shp"), ("All files", "*.*")],
            initialfile=f"{default_name}.shp",
        )
        if not shp_path:
            return

        try:
            conn = psycopg2.connect(
                host=cfg["db_host"], port=cfg["db_port"],
                user=cfg["db_user"], password=cfg["db_password"],
                dbname=cfg["db_name"], client_encoding="UTF8",
            )

            with conn.cursor() as cur:
                cur.execute(f'SELECT COUNT(*) FROM "{table}"')
                total = cur.fetchone()[0]

            if total == 0:
                messagebox.showinfo("提示", f"表 \"{table}\" 中无数据")
                conn.close()
                return

            self._log(f"正在导出表 [{table}] 共 {total} 条记录...")
            self.status_label.config(text=f"导出 {table}: {total} 条...")

            shape_type = shp.POLYLINE if is_line else shp.POLYGON
            w = shp.Writer(shp_path, shapeType=shape_type, encoding="utf-8")

            fields = LINE_SHP_FIELDS if is_line else POLYGON_SHP_FIELDS
            for fname, ftype, flen, fdec in fields:
                w.field(fname, ftype, flen, fdec)

            csv_rows = []
            exported = 0
            skipped = 0

            with conn.cursor() as cur:
                # 分批读取
                cur.execute(f'SELECT * FROM "{table}"')
                columns = [desc[0] for desc in cur.description]

                while True:
                    rows = cur.fetchmany(5000)
                    if not rows:
                        break

                    for row in rows:
                        rec = dict(zip(columns, row))
                        geom_json = rec.get("geom")
                        if not geom_json:
                            skipped += 1
                            continue

                        if isinstance(geom_json, str):
                            try:
                                geom_json = json.loads(geom_json)
                            except json.JSONDecodeError:
                                skipped += 1
                                continue

                        coords = overpass_geom_to_coords(
                            geom_json, "line" if is_line else "polygon")

                        if not coords or not coords[0]:
                            skipped += 1
                            continue

                        try:
                            if is_line:
                                w.line(coords)
                            else:
                                w.poly(coords)

                            w.record(
                                osm_id=rec.get("osm_id", 0) or 0,
                                osm_type=str(rec.get("osm_type", "") or "")[:10],
                                name=str(rec.get("name", "") or "")[:200],
                                sub_type=str(rec.get("sub_type", "") or "")[:50],
                            )

                            csv_row = {
                                "osm_id": rec.get("osm_id", ""),
                                "osm_type": rec.get("osm_type", ""),
                                "name": rec.get("name", ""),
                                "sub_type": rec.get("sub_type", ""),
                                "geom_wkt": overpass_geom_to_wkt(
                                    geom_json, "line" if is_line else "polygon"),
                            }
                            csv_rows.append(csv_row)
                            exported += 1
                        except Exception:
                            skipped += 1

            w.close()
            conn.close()

            # PRJ
            prj_path = shp_path.replace(".shp", ".prj")
            with open(prj_path, "w", encoding="utf-8") as f:
                f.write(PRJ_WGS84)

            # CSV
            csv_path = shp_path.replace(".shp", ".csv")
            import csv
            if csv_rows:
                with open(csv_path, "w", encoding="utf-8-sig", newline="") as f:
                    writer = csv.DictWriter(f, fieldnames=list(csv_rows[0].keys()))
                    writer.writeheader()
                    writer.writerows(csv_rows)

            self._log(f"导出完成: {exported} 条 (跳过 {skipped} 条)")
            self._log(f"SHP: {shp_path}")
            self._log(f"CSV: {csv_path}")
            self.status_label.config(text=f"导出完成: {exported} 条")
            messagebox.showinfo(
                "导出完成",
                f"{exported} 条记录 (跳过 {skipped} 条)\n\n"
                f"SHP: {shp_path}\nCSV: {csv_path}\n\n"
                "坐标系: WGS84 (EPSG:4326)")

        except Exception as e:
            self._log(f"导出失败: {e}\n{traceback.format_exc()}")
            messagebox.showerror("导出失败", str(e))

    # ============================================================
    # 日志 & 队列轮询
    # ============================================================

    def _log(self, msg):
        self.log_text.config(state=tk.NORMAL)
        ts = datetime.now().strftime("%H:%M:%S")
        self.log_text.insert(tk.END, f"[{ts}] {msg}\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)

    def _clear_log(self):
        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete("1.0", tk.END)
        self.log_text.config(state=tk.DISABLED)

    def _poll_queues(self):
        try:
            while True:
                msg = self.log_queue.get_nowait()
                if isinstance(msg, tuple):
                    kind, payload = msg
                    if kind == "log":
                        self._log(payload)
                    elif kind == "error":
                        self._log(f"❌ 错误: {payload}")
                        self.btn_start.config(state=tk.NORMAL)
                        self.btn_stop.config(state=tk.DISABLED)
                        self.status_label.config(text="出错", fg="#EF4444")
                    elif kind == "done":
                        self._log("✅ 全部完成!")
                        self.btn_start.config(state=tk.NORMAL)
                        self.btn_stop.config(state=tk.DISABLED)
                        self.status_label.config(text="完成", fg="#059669")
                        self.progress_var.set(100)
                else:
                    self._log(str(msg))
        except queue.Empty:
            pass

        try:
            while True:
                current, total, detail = self.progress_queue.get_nowait()
                if total > 0:
                    pct = int(current / total * 100)
                    self.progress_var.set(pct)
                    self.progress_label.config(
                        text=f"{current}/{total} — {detail}")
        except queue.Empty:
            pass

        self.after(200, self._poll_queues)

    def _on_close(self):
        self.stop_event.set()
        self.destroy()

# ============================================================
# 入口
# ============================================================

def show_splash():
    """绚丽开场动画 — OSM 版"""
    splash = tk.Tk()
    splash.overrideredirect(True)
    splash.attributes("-topmost", True)
    sw, sh = 560, 380
    sx = (splash.winfo_screenwidth() - sw) // 2
    sy = (splash.winfo_screenheight() - sh) // 2
    splash.geometry(f"{sw}x{sh}+{sx}+{sy}")
    splash.configure(bg="#0A0A1A")
    splash.attributes("-alpha", 0.0)

    canvas = tk.Canvas(splash, width=sw, height=sh, bg="#0A0A1A",
                       highlightthickness=0)
    canvas.pack(fill=tk.BOTH, expand=True)

    # 背景光晕
    for cx, cy, r, color in [
        (280, 140, 180, "#1A1040"), (180, 240, 120, "#221250"),
        (400, 100, 90, "#1E1145"), (100, 80, 60, "#2D1A60"),
        (460, 260, 70, "#251850"),
    ]:
        canvas.create_oval(cx-r, cy-r, cx+r, cy+r, fill=color, outline="")

    # 脉冲环
    ring1 = canvas.create_oval(100, 70, 460, 310, outline="#6C3CE0",
                                width=2, dash=(4, 8))
    ring2 = canvas.create_oval(120, 90, 440, 290, outline="#8B5CF6",
                                width=1, dash=(2, 16))

    # 标题
    title = canvas.create_text(280, 125, text="OSM 开放地图数据下载工具",
                                fill="#8B5CF6",
                                font=("Microsoft YaHei UI", 24, "bold"))
    subtitle = canvas.create_text(280, 168, text="OpenStreetMap Data Downloader",
                                   fill="#A78BFA", font=("Consolas", 13))

    # 装饰线
    canvas.create_line(160, 195, 400, 195, fill="#6C3CE0", width=1)
    canvas.create_line(190, 200, 370, 200, fill="#8B5CF6", width=2)

    # 开发者
    canvas.create_text(280, 240, text="开发者：白栋博",
                       fill="#C4B5FD",
                       font=("Microsoft YaHei UI", 13, "bold"))
    canvas.create_text(280, 270, text="微信：bdb15896810691",
                       fill="#A78BFA",
                       font=("Microsoft YaHei UI", 12))

    # 数据源说明
    canvas.create_text(280, 305, text="数据源: OpenStreetMap | Overpass API",
                       fill="#6D63B8",
                       font=("Microsoft YaHei UI", 8))

    # loading
    loading = canvas.create_text(280, 340, text="● 正在启动...",
                                  fill="#6C3CE0",
                                  font=("Microsoft YaHei UI", 9))

    # 粒子
    import random
    particles = []
    for _ in range(30):
        x = random.randint(20, sw-20)
        y = random.randint(20, sh-20)
        r = random.randint(1, 3)
        p = canvas.create_oval(
            x-r, y-r, x+r, y+r,
            fill=random.choice(["#8B5CF6","#A78BFA","#6C3CE0","#C4B5FD"]),
            outline="")
        particles.append((
            p, x, y,
            random.uniform(0, 2*math.pi),
            random.uniform(0.3, 1.2)
        ))

    # 淡入
    for a in [0.1, 0.2, 0.35, 0.5, 0.7, 0.85, 0.95, 1.0]:
        splash.attributes("-alpha", a)
        splash.update()
        time.sleep(0.03)

    # 动画循环
    start_t = time.time()
    angle = 0
    while time.time() - start_t < 3.0:
        angle += 0.05
        canvas.itemconfig(ring1, dash=(4+int(math.sin(angle)*2), 8))
        canvas.itemconfig(ring2, dash=(2, 16+int(math.sin(angle*1.5)*4)))
        for p, px, py, pa, ps in particles:
            nx = px + math.cos(pa + angle*ps) * 15 * math.sin(angle*0.7)
            ny = py + math.sin(pa + angle*ps) * 15 * math.cos(angle*0.7)
            canvas.coords(p, nx-1, ny-1, nx+1, ny+1)
        scale = 1 + math.sin(angle*1.3) * 0.02
        canvas.itemconfig(title, font=("Microsoft YaHei UI", int(24*scale), "bold"))
        dots = "●" * (1 + int((time.time()*3) % 4))
        canvas.itemconfig(loading, text=f"{dots} 正在启动...")
        splash.update()
        time.sleep(0.02)

    # 淡出
    for a in [0.9, 0.7, 0.5, 0.3, 0.15, 0.05, 0.0]:
        splash.attributes("-alpha", a)
        splash.update()
        time.sleep(0.02)

    splash.destroy()


def main():
    import traceback
    def _show_error(exc_type, exc_val, exc_tb):
        msg = "".join(traceback.format_exception(exc_type, exc_val, exc_tb))
        try:
            tk.messagebox.showerror("程序异常", f"请将此信息反馈给开发者：\n\n{msg[-2000:]}")
        except Exception:
            pass
    tk.Tk.report_callback_exception = _show_error

    show_splash()

    try:
        app = App()
        app.mainloop()
    except Exception as e:
        traceback.print_exc()
        try:
            tk.messagebox.showerror("启动失败", str(e))
        except Exception:
            pass

if __name__ == "__main__":
    main()
