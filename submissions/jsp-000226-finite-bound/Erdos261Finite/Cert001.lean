import Erdos261Finite.Cert000

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace Erdos261Finite

theorem cert_16041 : Represents 162 70 :=
  segment 12 162 70 174 120 (by rfl) cert_16029

theorem cert_16043 : Represents 160 98 :=
  segment 2 160 98 162 70 (by rfl) cert_16041

theorem cert_16069 : Represents 134 128 :=
  segment 26 134 128 160 98 (by rfl) cert_16043

theorem cert_16075 : Represents 128 2 :=
  segment 6 128 2 134 128 (by rfl) cert_16069

theorem cert_16081 : Represents 122 120 :=
  segment 6 122 120 128 2 (by rfl) cert_16075

theorem cert_16087 : Represents 123 121 :=
  segment 5 123 121 128 2 (by rfl) cert_16075

theorem cert_16092 : Represents 125 123 :=
  segment 3 125 123 128 98 (by rfl) cert_15975

theorem cert_16101 : Represents 126 124 :=
  segment 8 126 124 134 40 (by rfl) cert_874

theorem cert_16109 : Represents 127 125 :=
  segment 7 127 125 134 24 (by rfl) cert_15506

theorem cert_16118 : Represents 128 126 :=
  segment 8 128 126 136 56 (by rfl) cert_13239

theorem cert_16121 : Represents 192 106 :=
  segment 2 192 106 194 38 (by rfl) cert_15728

theorem cert_16139 : Represents 174 56 :=
  segment 18 174 56 192 106 (by rfl) cert_16121

theorem cert_16151 : Represents 162 94 :=
  segment 12 162 94 174 56 (by rfl) cert_16139

theorem cert_16184 : Represents 129 127 :=
  segment 33 129 127 162 94 (by rfl) cert_16151

theorem cert_16218 : Represents 152 138 :=
  segment 32 152 138 184 18 (by rfl) cert_16019

theorem cert_16228 : Represents 142 80 :=
  segment 10 142 80 152 138 (by rfl) cert_16218

theorem cert_16239 : Represents 131 129 :=
  segment 11 131 129 142 80 (by rfl) cert_16228

theorem cert_16268 : Represents 132 130 :=
  segment 28 132 130 160 96 (by rfl) cert_13532

theorem cert_16270 : Represents 133 131 :=
  segment 1 133 131 134 128 (by rfl) cert_16069

theorem cert_16279 : Represents 134 132 :=
  segment 8 134 132 142 104 (by rfl) cert_15961

theorem cert_16287 : Represents 135 133 :=
  segment 7 135 133 142 56 (by rfl) cert_15780

theorem cert_16310 : Represents 152 146 :=
  segment 22 152 146 174 120 (by rfl) cert_16029

theorem cert_16312 : Represents 150 112 :=
  segment 2 150 112 152 146 (by rfl) cert_16310

theorem cert_16326 : Represents 136 134 :=
  segment 14 136 134 150 112 (by rfl) cert_16312

theorem cert_16339 : Represents 148 146 :=
  segment 12 148 146 160 10 (by rfl) cert_15943

theorem cert_16350 : Represents 137 135 :=
  segment 11 137 135 148 146 (by rfl) cert_16339

theorem cert_16355 : Represents 138 136 :=
  segment 4 138 136 142 80 (by rfl) cert_16228

theorem cert_16367 : Represents 139 137 :=
  segment 11 139 137 150 112 (by rfl) cert_16312

theorem cert_16388 : Represents 140 138 :=
  segment 20 140 138 160 152 (by rfl) cert_14051

theorem cert_16390 : Represents 141 139 :=
  segment 1 141 139 142 136 (by rfl) cert_312

theorem cert_16393 : Represents 142 140 :=
  segment 2 142 140 144 130 (by rfl) cert_15959

theorem cert_16398 : Represents 150 88 :=
  segment 4 150 88 154 46 (by rfl) cert_300

theorem cert_16405 : Represents 143 141 :=
  segment 7 143 141 150 88 (by rfl) cert_16398

theorem cert_16424 : Represents 144 142 :=
  segment 18 144 142 162 94 (by rfl) cert_16151

theorem cert_16440 : Represents 145 143 :=
  segment 15 145 143 160 32 (by rfl) cert_682

theorem cert_16445 : Represents 146 144 :=
  segment 4 146 144 150 88 (by rfl) cert_16398

theorem cert_16449 : Represents 147 145 :=
  segment 3 147 145 150 120 (by rfl) cert_15490

theorem cert_16464 : Represents 149 147 :=
  segment 13 149 147 162 70 (by rfl) cert_16041

theorem cert_16467 : Represents 150 148 :=
  segment 2 150 148 152 138 (by rfl) cert_16218

theorem cert_16469 : Represents 151 149 :=
  segment 1 151 149 152 146 (by rfl) cert_16310

theorem cert_16502 : Represents 152 150 :=
  segment 32 152 150 184 50 (by rfl) cert_15456

theorem cert_16515 : Represents 258 102 :=
  segment 12 258 102 270 216 (by rfl) cert_15370

theorem cert_16541 : Represents 232 96 :=
  segment 26 232 96 258 102 (by rfl) cert_16515

theorem cert_16549 : Represents 224 96 :=
  segment 8 224 96 232 96 (by rfl) cert_16541

theorem cert_16559 : Represents 214 24 :=
  segment 10 214 24 224 96 (by rfl) cert_16549

theorem cert_16589 : Represents 184 114 :=
  segment 30 184 114 214 24 (by rfl) cert_16559

theorem cert_16605 : Represents 168 138 :=
  segment 16 168 138 184 114 (by rfl) cert_16589

theorem cert_16620 : Represents 153 151 :=
  segment 15 153 151 168 138 (by rfl) cert_16605

theorem cert_16627 : Represents 154 152 :=
  segment 6 154 152 160 66 (by rfl) cert_13215

theorem cert_16634 : Represents 264 250 :=
  segment 6 264 250 270 56 (by rfl) cert_15652

theorem cert_16640 : Represents 258 158 :=
  segment 6 258 158 264 250 (by rfl) cert_16634

theorem cert_16650 : Represents 248 224 :=
  segment 10 248 224 258 158 (by rfl) cert_16640

theorem cert_16706 : Represents 192 162 :=
  segment 56 192 162 248 224 (by rfl) cert_16650

theorem cert_16714 : Represents 184 72 :=
  segment 8 184 72 192 162 (by rfl) cert_16706

theorem cert_16726 : Represents 172 170 :=
  segment 12 172 170 184 72 (by rfl) cert_16714

theorem cert_16743 : Represents 155 153 :=
  segment 17 155 153 172 170 (by rfl) cert_16726

theorem cert_16748 : Represents 156 154 :=
  segment 4 156 154 160 98 (by rfl) cert_16043

theorem cert_16752 : Represents 157 155 :=
  segment 3 157 155 160 130 (by rfl) cert_294

theorem cert_16763 : Represents 158 156 :=
  segment 10 158 156 168 18 (by rfl) cert_674

theorem cert_16772 : Represents 166 152 :=
  segment 8 166 152 174 8 (by rfl) cert_13201

theorem cert_16779 : Represents 159 157 :=
  segment 7 159 157 166 152 (by rfl) cert_16772

theorem cert_16788 : Represents 176 40 :=
  segment 8 176 40 184 0 (by rfl) (zero_represents 184)

theorem cert_16804 : Represents 160 158 :=
  segment 16 160 158 176 40 (by rfl) cert_16788

theorem cert_16818 : Represents 161 159 :=
  segment 13 161 159 174 56 (by rfl) cert_16139

theorem cert_16834 : Represents 170 168 :=
  segment 14 170 168 184 72 (by rfl) cert_16714

theorem cert_16841 : Represents 163 161 :=
  segment 7 163 161 170 168 (by rfl) cert_16834

theorem cert_16844 : Represents 164 162 :=
  segment 2 164 162 166 152 (by rfl) cert_16772

theorem cert_16848 : Represents 165 163 :=
  segment 3 165 163 168 138 (by rfl) cert_16605

theorem cert_16859 : Represents 166 164 :=
  segment 10 166 164 176 56 (by rfl) cert_278

theorem cert_16869 : Represents 167 165 :=
  segment 9 167 165 176 40 (by rfl) cert_16788

theorem cert_16894 : Represents 168 166 :=
  segment 24 168 166 192 136 (by rfl) cert_15448

theorem cert_16900 : Represents 169 167 :=
  segment 5 169 167 174 48 (by rfl) cert_14037

theorem cert_16914 : Represents 202 182 :=
  segment 12 202 182 214 24 (by rfl) cert_16559

theorem cert_16945 : Represents 171 169 :=
  segment 31 171 169 202 182 (by rfl) cert_16914

theorem cert_16948 : Represents 173 171 :=
  segment 1 173 171 174 168 (by rfl) cert_13518

theorem cert_16951 : Represents 174 172 :=
  segment 2 174 172 176 162 (by rfl) cert_15927

theorem cert_16961 : Represents 175 173 :=
  segment 9 175 173 184 136 (by rfl) cert_15738

theorem cert_16980 : Represents 176 174 :=
  segment 18 176 174 194 30 (by rfl) cert_648

theorem cert_16996 : Represents 177 175 :=
  segment 15 177 175 192 106 (by rfl) cert_16121

theorem cert_17003 : Represents 178 176 :=
  segment 6 178 176 184 114 (by rfl) cert_16589

theorem cert_17011 : Represents 179 177 :=
  segment 7 179 177 186 46 (by rfl) cert_13189

theorem cert_17034 : Represents 181 179 :=
  segment 21 181 179 202 54 (by rfl) cert_15720

theorem cert_17045 : Represents 182 180 :=
  segment 10 182 180 192 58 (by rfl) cert_15730

theorem cert_17064 : Represents 358 328 :=
  segment 18 358 328 376 274 (by rfl) cert_15264

theorem cert_17070 : Represents 352 226 :=
  segment 6 352 226 358 328 (by rfl) cert_17064

theorem cert_17072 : Represents 350 320 :=
  segment 2 350 320 352 226 (by rfl) cert_17070

theorem cert_17092 : Represents 330 328 :=
  segment 20 330 328 350 320 (by rfl) cert_17072

theorem cert_17108 : Represents 314 142 :=
  segment 16 314 142 330 328 (by rfl) cert_17092

theorem cert_17124 : Represents 298 296 :=
  segment 16 298 296 314 142 (by rfl) cert_17108

theorem cert_17132 : Represents 290 70 :=
  segment 8 290 70 298 296 (by rfl) cert_17124

theorem cert_17150 : Represents 272 152 :=
  segment 18 272 152 290 70 (by rfl) cert_17132

theorem cert_17166 : Represents 256 250 :=
  segment 16 256 250 272 152 (by rfl) cert_17150

theorem cert_17182 : Represents 240 226 :=
  segment 16 240 226 256 250 (by rfl) cert_17166

theorem cert_17188 : Represents 234 232 :=
  segment 6 234 232 240 226 (by rfl) cert_17182

theorem cert_17239 : Represents 183 181 :=
  segment 51 183 181 234 232 (by rfl) cert_17188

theorem cert_17244 : Represents 198 72 :=
  segment 4 198 72 202 150 (by rfl) cert_15438

theorem cert_17258 : Represents 184 182 :=
  segment 14 184 182 198 72 (by rfl) cert_17244

theorem cert_17305 : Represents 464 378 :=
  segment 46 464 378 510 136 (by rfl) cert_12865

theorem cert_17327 : Represents 442 334 :=
  segment 22 442 334 464 378 (by rfl) cert_17305

theorem cert_17353 : Represents 416 386 :=
  segment 26 416 386 442 334 (by rfl) cert_17327

theorem cert_17355 : Represents 414 408 :=
  segment 2 414 408 416 386 (by rfl) cert_17353

theorem cert_17393 : Represents 376 104 :=
  segment 38 376 104 414 408 (by rfl) cert_17355

theorem cert_17409 : Represents 360 128 :=
  segment 16 360 128 376 104 (by rfl) cert_17393

theorem cert_17417 : Represents 352 128 :=
  segment 8 352 128 360 128 (by rfl) cert_17409

theorem cert_17479 : Represents 290 222 :=
  segment 62 290 222 352 128 (by rfl) cert_17417

theorem cert_17481 : Represents 288 200 :=
  segment 2 288 200 290 222 (by rfl) cert_17479

theorem cert_17531 : Represents 238 208 :=
  segment 50 238 208 288 200 (by rfl) cert_17481

theorem cert_17537 : Represents 232 18 :=
  segment 6 232 18 238 208 (by rfl) cert_17531

theorem cert_17545 : Represents 224 218 :=
  segment 8 224 218 232 18 (by rfl) cert_17537

theorem cert_17553 : Represents 216 64 :=
  segment 8 216 64 224 218 (by rfl) cert_17545

theorem cert_17584 : Represents 185 183 :=
  segment 31 185 183 216 64 (by rfl) cert_17553

theorem cert_17643 : Represents 214 200 :=
  segment 58 214 200 272 152 (by rfl) cert_17150

theorem cert_17645 : Represents 212 210 :=
  segment 2 212 210 214 200 (by rfl) cert_17643

theorem cert_17665 : Represents 192 130 :=
  segment 20 192 130 212 210 (by rfl) cert_17645

theorem cert_17671 : Represents 186 184 :=
  segment 6 186 184 192 130 (by rfl) cert_17665

theorem cert_17680 : Represents 206 192 :=
  segment 8 206 192 214 120 (by rfl) cert_13161

theorem cert_17699 : Represents 187 185 :=
  segment 19 187 185 206 192 (by rfl) cert_17680

theorem cert_17704 : Represents 188 186 :=
  segment 4 188 186 192 130 (by rfl) cert_17665

theorem cert_17708 : Represents 189 187 :=
  segment 3 189 187 192 162 (by rfl) cert_16706

theorem cert_17711 : Represents 222 80 :=
  segment 2 222 80 224 96 (by rfl) cert_16549

theorem cert_17717 : Represents 216 178 :=
  segment 6 216 178 222 80 (by rfl) cert_17711

theorem cert_17725 : Represents 208 154 :=
  segment 8 208 154 216 178 (by rfl) cert_17717

theorem cert_17743 : Represents 190 188 :=
  segment 18 190 188 208 154 (by rfl) cert_17725

theorem cert_17750 : Represents 226 166 :=
  segment 6 226 166 232 146 (by rfl) cert_222

theorem cert_17752 : Represents 224 154 :=
  segment 2 224 154 226 166 (by rfl) cert_17750

theorem cert_17785 : Represents 191 189 :=
  segment 33 191 189 224 154 (by rfl) cert_17752

theorem cert_17794 : Represents 200 170 :=
  segment 8 200 170 208 154 (by rfl) cert_17725

theorem cert_17802 : Represents 192 190 :=
  segment 8 192 190 200 170 (by rfl) cert_17794

theorem cert_17808 : Represents 193 191 :=
  segment 5 193 191 198 72 (by rfl) cert_17244

theorem cert_17817 : Represents 194 192 :=
  segment 8 194 192 202 182 (by rfl) cert_16914

theorem cert_17855 : Represents 195 193 :=
  segment 37 195 193 232 88 (by rfl) cert_610

theorem cert_17858 : Represents 196 194 :=
  segment 2 196 194 198 184 (by rfl) cert_15442

theorem cert_17862 : Represents 197 195 :=
  segment 3 197 195 200 170 (by rfl) cert_17794

theorem cert_17871 : Represents 198 196 :=
  segment 8 198 196 206 0 (by rfl) (zero_represents 206)

theorem cert_17878 : Represents 208 10 :=
  segment 6 208 10 214 0 (by rfl) (zero_represents 214)

theorem cert_17887 : Represents 199 197 :=
  segment 9 199 197 208 10 (by rfl) cert_17878

theorem cert_17896 : Represents 200 198 :=
  segment 8 200 198 208 10 (by rfl) cert_17878

theorem cert_17912 : Represents 201 199 :=
  segment 15 201 199 216 0 (by rfl) (zero_represents 216)

theorem cert_17919 : Represents 226 190 :=
  segment 6 226 190 232 96 (by rfl) cert_16541

theorem cert_17943 : Represents 202 200 :=
  segment 24 202 200 226 190 (by rfl) cert_17919

theorem cert_17955 : Represents 203 201 :=
  segment 11 203 201 214 200 (by rfl) cert_17643

theorem cert_17958 : Represents 204 202 :=
  segment 2 204 202 206 192 (by rfl) cert_17680

theorem cert_17970 : Represents 205 203 :=
  segment 11 205 203 216 64 (by rfl) cert_17553

theorem cert_17987 : Represents 206 204 :=
  segment 16 206 204 222 0 (by rfl) (zero_represents 222)

theorem cert_17990 : Represents 216 90 :=
  segment 2 216 90 218 142 (by rfl) cert_15422

theorem cert_17999 : Represents 207 205 :=
  segment 9 207 205 216 90 (by rfl) cert_17990

theorem cert_18008 : Represents 208 206 :=
  segment 8 208 206 216 50 (by rfl) cert_13159

theorem cert_18066 : Represents 209 207 :=
  segment 57 209 207 266 214 (by rfl) cert_15374

theorem cert_18073 : Represents 210 208 :=
  segment 6 210 208 216 178 (by rfl) cert_17717

theorem cert_18079 : Represents 211 209 :=
  segment 5 211 209 216 90 (by rfl) cert_17990

theorem cert_18092 : Represents 213 211 :=
  segment 11 213 211 224 154 (by rfl) cert_17752

theorem cert_18101 : Represents 214 212 :=
  segment 8 214 212 222 80 (by rfl) cert_17711

theorem cert_18137 : Represents 215 213 :=
  segment 35 215 213 250 78 (by rfl) cert_13125

theorem cert_18180 : Represents 216 214 :=
  segment 42 216 214 258 102 (by rfl) cert_16515

theorem cert_18190 : Represents 217 215 :=
  segment 9 217 215 226 190 (by rfl) cert_17919

theorem cert_18197 : Represents 224 194 :=
  segment 6 224 194 230 0 (by rfl) (zero_represents 230)

theorem cert_18203 : Represents 218 216 :=
  segment 6 218 216 224 194 (by rfl) cert_18197

theorem cert_18211 : Represents 219 217 :=
  segment 7 219 217 226 166 (by rfl) cert_17750

theorem cert_18216 : Represents 220 218 :=
  segment 4 220 218 224 162 (by rfl) cert_230

theorem cert_18220 : Represents 221 219 :=
  segment 3 221 219 224 194 (by rfl) cert_18197

theorem cert_18231 : Represents 222 220 :=
  segment 10 222 220 232 18 (by rfl) cert_17537

theorem cert_18233 : Represents 223 221 :=
  segment 1 223 221 224 218 (by rfl) cert_17545

theorem cert_18258 : Represents 224 222 :=
  segment 24 224 222 248 224 (by rfl) cert_16650

theorem cert_18267 : Represents 246 120 :=
  segment 8 246 120 254 112 (by rfl) cert_15668

theorem cert_18288 : Represents 225 223 :=
  segment 21 225 223 246 120 (by rfl) cert_18267

theorem cert_18313 : Represents 226 224 :=
  segment 24 226 224 250 174 (by rfl) cert_204

theorem cert_18317 : Represents 227 225 :=
  segment 3 227 225 230 200 (by rfl) cert_15410

theorem cert_18366 : Represents 256 226 :=
  segment 48 256 226 304 106 (by rfl) cert_150

theorem cert_18394 : Represents 228 226 :=
  segment 28 228 226 256 226 (by rfl) cert_18366

theorem cert_18424 : Represents 229 227 :=
  segment 29 229 227 258 158 (by rfl) cert_16640

theorem cert_18433 : Represents 456 210 :=
  segment 8 456 210 464 88 (by rfl) cert_15176

theorem cert_18459 : Represents 430 176 :=
  segment 26 430 176 456 210 (by rfl) cert_18433

theorem cert_18495 : Represents 394 392 :=
  segment 36 394 392 430 176 (by rfl) cert_18459

theorem cert_18505 : Represents 384 258 :=
  segment 10 384 258 394 392 (by rfl) cert_18495

theorem cert_18507 : Represents 382 352 :=
  segment 2 382 352 384 258 (by rfl) cert_18505

theorem cert_18561 : Represents 328 288 :=
  segment 54 328 288 382 352 (by rfl) cert_18507

theorem cert_18563 : Represents 326 72 :=
  segment 2 326 72 328 288 (by rfl) cert_18561

theorem cert_18607 : Represents 282 206 :=
  segment 44 282 206 326 72 (by rfl) cert_18563

theorem cert_18611 : Represents 278 240 :=
  segment 4 278 240 282 206 (by rfl) cert_18607

theorem cert_18619 : Represents 270 144 :=
  segment 8 270 144 278 240 (by rfl) cert_18611

theorem cert_18659 : Represents 230 228 :=
  segment 40 230 228 270 144 (by rfl) cert_18619

theorem cert_18678 : Represents 248 210 :=
  segment 18 248 210 266 54 (by rfl) cert_15656

theorem cert_18695 : Represents 231 229 :=
  segment 17 231 229 248 210 (by rfl) cert_18678

theorem cert_18728 : Represents 232 230 :=
  segment 32 232 230 264 146 (by rfl) cert_15658

theorem cert_18731 : Represents 256 128 :=
  segment 2 256 128 258 254 (by rfl) cert_15664

theorem cert_18754 : Represents 233 231 :=
  segment 23 233 231 256 128 (by rfl) cert_18731

theorem cert_18759 : Represents 235 233 :=
  segment 3 235 233 238 208 (by rfl) cert_17531

theorem cert_18768 : Represents 456 248 :=
  segment 8 456 248 464 378 (by rfl) cert_17305

theorem cert_18774 : Represents 450 286 :=
  segment 6 450 286 456 248 (by rfl) cert_18768

theorem cert_18862 : Represents 362 118 :=
  segment 88 362 118 450 286 (by rfl) cert_18774

theorem cert_18864 : Represents 360 210 :=
  segment 2 360 210 362 118 (by rfl) cert_18862

theorem cert_18880 : Represents 344 282 :=
  segment 16 344 282 360 210 (by rfl) cert_18864

theorem cert_18988 : Represents 236 234 :=
  segment 108 236 234 344 282 (by rfl) cert_18880

theorem cert_18998 : Represents 237 235 :=
  segment 9 237 235 246 144 (by rfl) cert_13129

theorem cert_19001 : Represents 238 236 :=
  segment 2 238 236 240 226 (by rfl) cert_17182

theorem cert_19035 : Represents 239 237 :=
  segment 33 239 237 272 138 (by rfl) cert_13103

theorem cert_19044 : Represents 240 238 :=
  segment 8 240 238 248 210 (by rfl) cert_18678

theorem cert_19050 : Represents 241 239 :=
  segment 5 241 239 246 120 (by rfl) cert_18267

theorem cert_19067 : Represents 248 242 :=
  segment 16 248 242 264 120 (by rfl) cert_15376

theorem cert_19073 : Represents 242 240 :=
  segment 6 242 240 248 242 (by rfl) cert_19067

theorem cert_19087 : Represents 243 241 :=
  segment 13 243 241 256 128 (by rfl) cert_18731

theorem cert_19090 : Represents 256 130 :=
  segment 2 256 130 258 6 (by rfl) cert_15382

theorem cert_19102 : Represents 244 242 :=
  segment 12 244 242 256 130 (by rfl) cert_19090

theorem cert_19146 : Represents 245 243 :=
  segment 43 245 243 288 200 (by rfl) cert_17481

theorem cert_19149 : Represents 252 250 :=
  segment 2 252 250 254 240 (by rfl) cert_13121

theorem cert_19155 : Represents 246 244 :=
  segment 6 246 244 252 250 (by rfl) cert_19149

theorem cert_19157 : Represents 247 245 :=
  segment 1 247 245 248 242 (by rfl) cert_19067

theorem cert_19164 : Represents 248 246 :=
  segment 6 248 246 254 0 (by rfl) (zero_represents 254)

theorem cert_19173 : Represents 270 192 :=
  segment 8 270 192 278 240 (by rfl) cert_18611

theorem cert_19187 : Represents 256 2 :=
  segment 14 256 2 270 192 (by rfl) cert_19173

theorem cert_19194 : Represents 249 247 :=
  segment 7 249 247 256 2 (by rfl) cert_19187

theorem cert_19201 : Represents 250 248 :=
  segment 6 250 248 256 2 (by rfl) cert_19187

theorem cert_19207 : Represents 251 249 :=
  segment 5 251 249 256 130 (by rfl) cert_19090

theorem cert_19212 : Represents 253 251 :=
  segment 3 253 251 256 226 (by rfl) cert_18366

theorem cert_19237 : Represents 254 252 :=
  segment 24 254 252 278 112 (by rfl) cert_15644

theorem cert_19239 : Represents 255 253 :=
  segment 1 255 253 256 250 (by rfl) cert_17166

theorem cert_19256 : Represents 368 106 :=
  segment 16 368 106 384 0 (by rfl) (zero_represents 384)

theorem cert_19280 : Represents 344 64 :=
  segment 24 344 64 368 106 (by rfl) cert_19256

theorem cert_19288 : Represents 336 122 :=
  segment 8 336 122 344 64 (by rfl) cert_19280

theorem cert_19294 : Represents 330 54 :=
  segment 6 330 54 336 122 (by rfl) cert_19288

theorem cert_19304 : Represents 320 184 :=
  segment 10 320 184 330 54 (by rfl) cert_19294

theorem cert_19312 : Represents 312 306 :=
  segment 8 312 306 320 184 (by rfl) cert_19304

theorem cert_19368 : Represents 256 254 :=
  segment 56 256 254 312 306 (by rfl) cert_19312

theorem cert_19383 : Represents 442 174 :=
  segment 14 442 174 456 248 (by rfl) cert_18768

theorem cert_19441 : Represents 384 128 :=
  segment 58 384 128 442 174 (by rfl) cert_19383

theorem cert_19465 : Represents 360 50 :=
  segment 24 360 50 384 128 (by rfl) cert_19441

theorem cert_19497 : Represents 328 42 :=
  segment 32 328 42 360 50 (by rfl) cert_19465

theorem cert_19521 : Represents 304 290 :=
  segment 24 304 290 328 42 (by rfl) cert_19497

theorem cert_19568 : Represents 257 255 :=
  segment 47 257 255 304 290 (by rfl) cert_19521

theorem cert_19600 : Represents 2912 2560 :=
  segment 30 2912 2560 2942 1472 (by rfl) cert_10433

theorem cert_19624 : Represents 2888 2656 :=
  segment 24 2888 2656 2912 2560 (by rfl) cert_19600

theorem cert_19656 : Represents 2856 2058 :=
  segment 32 2856 2058 2888 2656 (by rfl) cert_19624

theorem cert_19682 : Represents 2830 1456 :=
  segment 26 2830 1456 2856 2058 (by rfl) cert_19656

theorem cert_19752 : Represents 2760 2464 :=
  segment 70 2760 2464 2830 1456 (by rfl) cert_19682

theorem cert_19760 : Represents 2752 1440 :=
  segment 8 2752 1440 2760 2464 (by rfl) cert_19752

theorem cert_19890 : Represents 2622 1104 :=
  segment 130 2622 1104 2752 1440 (by rfl) cert_19760

theorem cert_19952 : Represents 2560 408 :=
  segment 62 2560 408 2622 1104 (by rfl) cert_19890

theorem cert_20110 : Represents 2402 1446 :=
  segment 158 2402 1446 2560 408 (by rfl) cert_19952

theorem cert_20366 : Represents 2146 1438 :=
  segment 256 2146 1438 2402 1446 (by rfl) cert_20110

theorem cert_20456 : Represents 2056 1834 :=
  segment 90 2056 1834 2146 1438 (by rfl) cert_20366

theorem cert_20538 : Represents 1974 1320 :=
  segment 82 1974 1320 2056 1834 (by rfl) cert_20456

theorem cert_20558 : Represents 1954 1350 :=
  segment 20 1954 1350 1974 1320 (by rfl) cert_20538

theorem cert_20578 : Represents 1934 1200 :=
  segment 20 1934 1200 1954 1350 (by rfl) cert_20558

theorem cert_20600 : Represents 1912 1394 :=
  segment 22 1912 1394 1934 1200 (by rfl) cert_20578

theorem cert_20610 : Represents 1902 736 :=
  segment 10 1902 736 1912 1394 (by rfl) cert_20600

theorem cert_20688 : Represents 1824 1570 :=
  segment 78 1824 1570 1902 736 (by rfl) cert_20610

theorem cert_20704 : Represents 1808 618 :=
  segment 16 1808 618 1824 1570 (by rfl) cert_20688

theorem cert_20722 : Represents 1790 1000 :=
  segment 18 1790 1000 1808 618 (by rfl) cert_20704

theorem cert_20752 : Represents 1760 1184 :=
  segment 30 1760 1184 1790 1000 (by rfl) cert_20722

theorem cert_20848 : Represents 1664 1226 :=
  segment 96 1664 1226 1760 1184 (by rfl) cert_20752

theorem cert_20904 : Represents 1608 1120 :=
  segment 56 1608 1120 1664 1226 (by rfl) cert_20848

theorem cert_20920 : Represents 1592 498 :=
  segment 16 1592 498 1608 1120 (by rfl) cert_20904

theorem cert_20944 : Represents 1568 1474 :=
  segment 24 1568 1474 1592 498 (by rfl) cert_20920

theorem cert_20962 : Represents 1550 1288 :=
  segment 18 1550 1288 1568 1474 (by rfl) cert_20944

theorem cert_21058 : Represents 1454 480 :=
  segment 96 1454 480 1550 1288 (by rfl) cert_20962

theorem cert_21134 : Represents 1378 166 :=
  segment 76 1378 166 1454 480 (by rfl) cert_21058

theorem cert_21138 : Represents 1374 1128 :=
  segment 4 1374 1128 1378 166 (by rfl) cert_21134

theorem cert_21204 : Represents 1308 1306 :=
  segment 66 1308 1306 1374 1128 (by rfl) cert_21138

theorem cert_21230 : Represents 1282 518 :=
  segment 26 1282 518 1308 1306 (by rfl) cert_21204

theorem cert_21256 : Represents 1256 1002 :=
  segment 26 1256 1002 1282 518 (by rfl) cert_21230

theorem cert_21258 : Represents 1254 1192 :=
  segment 2 1254 1192 1256 1002 (by rfl) cert_21256

theorem cert_21414 : Represents 1098 22 :=
  segment 156 1098 22 1254 1192 (by rfl) cert_21258

theorem cert_21526 : Represents 986 718 :=
  segment 112 986 718 1098 22 (by rfl) cert_21414

theorem cert_21542 : Represents 970 790 :=
  segment 16 970 790 986 718 (by rfl) cert_21526

theorem cert_21554 : Represents 958 448 :=
  segment 12 958 448 970 790 (by rfl) cert_21542

theorem cert_21658 : Represents 854 176 :=
  segment 104 854 176 958 448 (by rfl) cert_21554

theorem cert_21686 : Represents 826 654 :=
  segment 28 826 654 854 176 (by rfl) cert_21658

theorem cert_21710 : Represents 802 734 :=
  segment 24 802 734 826 654 (by rfl) cert_21686

theorem cert_21752 : Represents 760 474 :=
  segment 42 760 474 802 734 (by rfl) cert_21710

theorem cert_21760 : Represents 752 58 :=
  segment 8 752 58 760 474 (by rfl) cert_21752

theorem cert_21798 : Represents 714 438 :=
  segment 38 714 438 752 58 (by rfl) cert_21760

theorem cert_21810 : Represents 702 312 :=
  segment 12 702 312 714 438 (by rfl) cert_21798

theorem cert_21826 : Represents 686 680 :=
  segment 16 686 680 702 312 (by rfl) cert_21810

theorem cert_21832 : Represents 680 96 :=
  segment 6 680 96 686 680 (by rfl) cert_21826

theorem cert_21848 : Represents 664 26 :=
  segment 16 664 26 680 96 (by rfl) cert_21832

theorem cert_21912 : Represents 600 594 :=
  segment 64 600 594 664 26 (by rfl) cert_21848

theorem cert_21936 : Represents 576 418 :=
  segment 24 576 418 600 594 (by rfl) cert_21912

theorem cert_21966 : Represents 546 446 :=
  segment 30 546 446 576 418 (by rfl) cert_21936

theorem cert_21968 : Represents 544 384 :=
  segment 2 544 384 546 446 (by rfl) cert_21966

theorem cert_21976 : Represents 536 474 :=
  segment 8 536 474 544 384 (by rfl) cert_21968

theorem cert_22000 : Represents 512 490 :=
  segment 24 512 490 536 474 (by rfl) cert_21976

theorem cert_22010 : Represents 502 248 :=
  segment 10 502 248 512 490 (by rfl) cert_22000

theorem cert_22016 : Represents 496 346 :=
  segment 6 496 346 502 248 (by rfl) cert_22010

theorem cert_22038 : Represents 474 46 :=
  segment 22 474 46 496 346 (by rfl) cert_22016

theorem cert_22064 : Represents 448 26 :=
  segment 26 448 26 474 46 (by rfl) cert_22038

theorem cert_22098 : Represents 414 16 :=
  segment 34 414 16 448 26 (by rfl) cert_22064

theorem cert_22104 : Represents 408 378 :=
  segment 6 408 378 414 16 (by rfl) cert_22098

theorem cert_22106 : Represents 406 400 :=
  segment 2 406 400 408 378 (by rfl) cert_22104

theorem cert_22120 : Represents 392 384 :=
  segment 14 392 384 406 400 (by rfl) cert_22106

theorem cert_22136 : Represents 376 370 :=
  segment 16 376 370 392 384 (by rfl) cert_22120

theorem cert_22160 : Represents 352 322 :=
  segment 24 352 322 376 370 (by rfl) cert_22136

theorem cert_22200 : Represents 312 274 :=
  segment 40 312 274 352 322 (by rfl) cert_22160

theorem cert_22253 : Represents 259 257 :=
  segment 53 259 257 312 274 (by rfl) cert_22200

theorem cert_22264 : Represents 260 258 :=
  segment 10 260 258 270 192 (by rfl) cert_19173

theorem cert_22267 : Represents 342 328 :=
  segment 2 342 328 344 282 (by rfl) cert_18880

theorem cert_22279 : Represents 330 278 :=
  segment 12 330 278 342 328 (by rfl) cert_22267

theorem cert_22289 : Represents 320 138 :=
  segment 10 320 138 330 278 (by rfl) cert_22279

theorem cert_22321 : Represents 288 66 :=
  segment 32 288 66 320 138 (by rfl) cert_22289

theorem cert_22329 : Represents 280 250 :=
  segment 8 280 250 288 66 (by rfl) cert_22321

theorem cert_22348 : Represents 261 259 :=
  segment 19 261 259 280 250 (by rfl) cert_22329

theorem cert_22351 : Represents 262 260 :=
  segment 2 262 260 264 250 (by rfl) cert_16634

theorem cert_22364 : Represents 276 274 :=
  segment 12 276 274 288 74 (by rfl) cert_15352

theorem cert_22377 : Represents 263 261 :=
  segment 13 263 261 276 274 (by rfl) cert_22364

theorem cert_22394 : Represents 264 262 :=
  segment 16 264 262 280 114 (by rfl) cert_15360

theorem cert_22400 : Represents 265 263 :=
  segment 5 265 263 270 144 (by rfl) cert_18619

theorem cert_22417 : Represents 266 264 :=
  segment 16 266 264 282 206 (by rfl) cert_18607

theorem cert_22447 : Represents 267 265 :=
  segment 29 267 265 296 210 (by rfl) cert_15626

theorem cert_22460 : Represents 268 266 :=
  segment 12 268 266 280 168 (by rfl) cert_15642

theorem cert_22470 : Represents 269 267 :=
  segment 9 269 267 278 168 (by rfl) cert_15362

theorem cert_22479 : Represents 344 40 :=
  segment 8 344 40 352 128 (by rfl) cert_17417

theorem cert_22503 : Represents 320 314 :=
  segment 24 320 314 344 40 (by rfl) cert_22479

theorem cert_22521 : Represents 302 48 :=
  segment 18 302 48 320 314 (by rfl) cert_22503

theorem cert_22553 : Represents 270 268 :=
  segment 32 270 268 302 48 (by rfl) cert_22521

theorem cert_22565 : Represents 271 269 :=
  segment 11 271 269 282 174 (by rfl) cert_15358

theorem cert_22614 : Represents 272 270 :=
  segment 48 272 270 320 184 (by rfl) cert_19304

theorem cert_22621 : Represents 288 32 :=
  segment 6 288 32 294 0 (by rfl) (zero_represents 294)

theorem cert_22636 : Represents 273 271 :=
  segment 15 273 271 288 32 (by rfl) cert_22621

theorem cert_22657 : Represents 274 272 :=
  segment 20 274 272 294 96 (by rfl) cert_15346

theorem cert_22671 : Represents 275 273 :=
  segment 13 275 273 288 32 (by rfl) cert_22621

theorem cert_22676 : Represents 277 275 :=
  segment 3 277 275 280 250 (by rfl) cert_22329

theorem cert_22701 : Represents 320 130 :=
  segment 24 320 130 344 64 (by rfl) cert_19280

theorem cert_22743 : Represents 278 276 :=
  segment 42 278 276 320 130 (by rfl) cert_22701

theorem cert_22800 : Represents 2504 2432 :=
  segment 56 2504 2432 2560 2154 (by rfl) cert_10815

theorem cert_22902 : Represents 2402 958 :=
  segment 102 2402 958 2504 2432 (by rfl) cert_22800

theorem cert_23158 : Represents 2146 710 :=
  segment 256 2146 710 2402 958 (by rfl) cert_22902

theorem cert_23248 : Represents 2056 224 :=
  segment 90 2056 224 2146 710 (by rfl) cert_23158

theorem cert_23330 : Represents 1974 656 :=
  segment 82 1974 656 2056 224 (by rfl) cert_23248

theorem cert_23350 : Represents 1954 606 :=
  segment 20 1954 606 1974 656 (by rfl) cert_23330

theorem cert_23370 : Represents 1934 736 :=
  segment 20 1934 736 1954 606 (by rfl) cert_23350

theorem cert_23402 : Represents 1902 1168 :=
  segment 32 1902 1168 1934 736 (by rfl) cert_23370

theorem cert_23474 : Represents 1830 1768 :=
  segment 72 1830 1768 1902 1168 (by rfl) cert_23402

theorem cert_23480 : Represents 1824 256 :=
  segment 6 1824 256 1830 1768 (by rfl) cert_23474

theorem cert_23496 : Represents 1808 1192 :=
  segment 16 1808 1192 1824 256 (by rfl) cert_23480

theorem cert_23578 : Represents 1726 952 :=
  segment 82 1726 952 1808 1192 (by rfl) cert_23496

theorem cert_23606 : Represents 1698 614 :=
  segment 28 1698 614 1726 952 (by rfl) cert_23578

theorem cert_23638 : Represents 1666 94 :=
  segment 32 1666 94 1698 614 (by rfl) cert_23606

theorem cert_23664 : Represents 1640 1184 :=
  segment 26 1640 1184 1666 94 (by rfl) cert_23638

theorem cert_23726 : Represents 1578 726 :=
  segment 62 1578 726 1640 1184 (by rfl) cert_23664

theorem cert_23736 : Represents 1568 96 :=
  segment 10 1568 96 1578 726 (by rfl) cert_23726

theorem cert_23810 : Represents 1494 1144 :=
  segment 74 1494 1144 1568 96 (by rfl) cert_23736

theorem cert_23850 : Represents 1454 976 :=
  segment 40 1454 976 1494 1144 (by rfl) cert_23810

theorem cert_23880 : Represents 1424 440 :=
  segment 30 1424 440 1454 976 (by rfl) cert_23850

theorem cert_23894 : Represents 1410 6 :=
  segment 14 1410 6 1424 440 (by rfl) cert_23880

theorem cert_23930 : Represents 1374 248 :=
  segment 36 1374 248 1410 6 (by rfl) cert_23894

theorem cert_24000 : Represents 1304 82 :=
  segment 70 1304 82 1374 248 (by rfl) cert_23930

theorem cert_24022 : Represents 1282 766 :=
  segment 22 1282 766 1304 82 (by rfl) cert_24000

theorem cert_24048 : Represents 1256 256 :=
  segment 26 1256 256 1282 766 (by rfl) cert_24022

theorem cert_24050 : Represents 1254 64 :=
  segment 2 1254 64 1256 256 (by rfl) cert_24048

theorem cert_24096 : Represents 1208 114 :=
  segment 46 1208 114 1254 64 (by rfl) cert_24050

theorem cert_24144 : Represents 1160 1130 :=
  segment 48 1160 1130 1208 114 (by rfl) cert_24096

theorem cert_24206 : Represents 1098 1078 :=
  segment 62 1098 1078 1160 1130 (by rfl) cert_24144

theorem cert_24274 : Represents 1030 568 :=
  segment 68 1030 568 1098 1078 (by rfl) cert_24206

theorem cert_24318 : Represents 986 270 :=
  segment 44 986 270 1030 568 (by rfl) cert_24274

theorem cert_24334 : Represents 970 182 :=
  segment 16 970 182 986 270 (by rfl) cert_24318

theorem cert_24352 : Represents 952 232 :=
  segment 18 952 232 970 182 (by rfl) cert_24334

theorem cert_24398 : Represents 906 694 :=
  segment 46 906 694 952 232 (by rfl) cert_24352

theorem cert_24450 : Represents 854 680 :=
  segment 52 854 680 906 694 (by rfl) cert_24398

theorem cert_24478 : Represents 826 174 :=
  segment 28 826 174 854 680 (by rfl) cert_24450

theorem cert_24534 : Represents 770 638 :=
  segment 56 770 638 826 174 (by rfl) cert_24478

theorem cert_24552 : Represents 752 696 :=
  segment 18 752 696 770 638 (by rfl) cert_24534

theorem cert_24590 : Represents 714 278 :=
  segment 38 714 278 752 696 (by rfl) cert_24552

theorem cert_24592 : Represents 712 426 :=
  segment 2 712 426 714 278 (by rfl) cert_24590

theorem cert_24602 : Represents 702 392 :=
  segment 10 702 392 712 426 (by rfl) cert_24592

theorem cert_24618 : Represents 686 8 :=
  segment 16 686 8 702 392 (by rfl) cert_24602

theorem cert_24624 : Represents 680 586 :=
  segment 6 680 586 686 8 (by rfl) cert_24618

theorem cert_24640 : Represents 664 640 :=
  segment 16 664 640 680 586 (by rfl) cert_24624

theorem cert_24650 : Represents 654 304 :=
  segment 10 654 304 664 640 (by rfl) cert_24640

theorem cert_24694 : Represents 610 294 :=
  segment 44 610 294 654 304 (by rfl) cert_24650

theorem cert_24760 : Represents 544 162 :=
  segment 66 544 162 610 294 (by rfl) cert_24694

theorem cert_24778 : Represents 526 104 :=
  segment 18 526 104 544 162 (by rfl) cert_24760

theorem cert_24792 : Represents 512 24 :=
  segment 14 512 24 526 104 (by rfl) cert_24778

theorem cert_24864 : Represents 440 314 :=
  segment 72 440 314 512 24 (by rfl) cert_24792

theorem cert_24890 : Represents 414 400 :=
  segment 26 414 400 440 314 (by rfl) cert_24864

theorem cert_24912 : Represents 392 10 :=
  segment 22 392 10 414 400 (by rfl) cert_24890

theorem cert_24944 : Represents 360 346 :=
  segment 32 360 346 392 10 (by rfl) cert_24912

theorem cert_24952 : Represents 352 32 :=
  segment 8 352 32 360 346 (by rfl) cert_24944

theorem cert_24954 : Represents 350 96 :=
  segment 2 350 96 352 32 (by rfl) cert_24952

theorem cert_24992 : Represents 312 40 :=
  segment 38 312 40 350 96 (by rfl) cert_24954

theorem cert_25025 : Represents 279 277 :=
  segment 33 279 277 312 40 (by rfl) cert_24992

theorem cert_25036 : Represents 280 278 :=
  segment 10 280 278 290 222 (by rfl) cert_17479

theorem cert_25044 : Represents 281 279 :=
  segment 7 281 279 288 66 (by rfl) cert_22321

theorem cert_25051 : Represents 282 280 :=
  segment 6 282 280 288 34 (by rfl) cert_13087

theorem cert_25059 : Represents 283 281 :=
  segment 7 283 281 290 70 (by rfl) cert_17132

theorem cert_25082 : Represents 392 138 :=
  segment 22 392 138 414 16 (by rfl) cert_22098

theorem cert_25090 : Represents 384 40 :=
  segment 8 384 40 392 138 (by rfl) cert_25082

theorem cert_25156 : Represents 318 96 :=
  segment 66 318 96 384 40 (by rfl) cert_25090

theorem cert_25190 : Represents 284 282 :=
  segment 34 284 282 318 96 (by rfl) cert_25156

theorem cert_25218 : Represents 285 283 :=
  segment 27 285 283 312 40 (by rfl) cert_24992

theorem cert_25261 : Represents 286 284 :=
  segment 42 286 284 328 288 (by rfl) cert_18561

theorem cert_25293 : Represents 287 285 :=
  segment 31 287 285 318 96 (by rfl) cert_25156

theorem cert_25308 : Represents 314 270 :=
  segment 14 314 270 328 42 (by rfl) cert_19497

theorem cert_25318 : Represents 304 232 :=
  segment 10 304 232 314 270 (by rfl) cert_25308

theorem cert_25334 : Represents 288 286 :=
  segment 16 288 286 304 232 (by rfl) cert_25318

theorem cert_25340 : Represents 289 287 :=
  segment 5 289 287 294 168 (by rfl) cert_160

theorem cert_25361 : Represents 386 134 :=
  segment 20 386 134 406 0 (by rfl) (zero_represents 406)

theorem cert_25363 : Represents 384 130 :=
  segment 2 384 130 386 134 (by rfl) cert_25361

theorem cert_25373 : Represents 374 48 :=
  segment 10 374 48 384 130 (by rfl) cert_25363

theorem cert_25393 : Represents 354 70 :=
  segment 20 354 70 374 48 (by rfl) cert_25373

theorem cert_25397 : Represents 350 224 :=
  segment 4 350 224 354 70 (by rfl) cert_25393

theorem cert_25403 : Represents 344 90 :=
  segment 6 344 90 350 224 (by rfl) cert_25397

theorem cert_25417 : Represents 330 22 :=
  segment 14 330 22 344 90 (by rfl) cert_25403

theorem cert_25445 : Represents 302 296 :=
  segment 28 302 296 330 22 (by rfl) cert_25417

theorem cert_25457 : Represents 290 288 :=
  segment 12 290 288 302 296 (by rfl) cert_25445

theorem cert_25476 : Represents 302 176 :=
  segment 18 302 176 320 138 (by rfl) cert_22289

theorem cert_25487 : Represents 291 289 :=
  segment 11 291 289 302 176 (by rfl) cert_25476

theorem cert_25530 : Represents 350 104 :=
  segment 42 350 104 392 10 (by rfl) cert_24912

theorem cert_25568 : Represents 312 250 :=
  segment 38 312 250 350 104 (by rfl) cert_25530

theorem cert_25588 : Represents 292 290 :=
  segment 20 292 290 312 250 (by rfl) cert_25568

theorem cert_25600 : Represents 293 291 :=
  segment 11 293 291 304 232 (by rfl) cert_25318

theorem cert_25603 : Represents 412 410 :=
  segment 2 412 410 414 400 (by rfl) cert_24890

theorem cert_25663 : Represents 352 98 :=
  segment 60 352 98 412 410 (by rfl) cert_25603

theorem cert_25685 : Represents 330 150 :=
  segment 22 330 150 352 98 (by rfl) cert_25663

theorem cert_25695 : Represents 320 258 :=
  segment 10 320 258 330 150 (by rfl) cert_25685

theorem cert_25697 : Represents 318 224 :=
  segment 2 318 224 320 258 (by rfl) cert_25695

theorem cert_25721 : Represents 294 292 :=
  segment 24 294 292 318 224 (by rfl) cert_25697

theorem cert_25739 : Represents 295 293 :=
  segment 17 295 293 312 274 (by rfl) cert_22200

theorem cert_25746 : Represents 296 294 :=
  segment 6 296 294 302 48 (by rfl) cert_22521

theorem cert_25752 : Represents 297 295 :=
  segment 5 297 295 302 176 (by rfl) cert_25476

theorem cert_25782 : Represents 334 208 :=
  segment 28 334 208 362 118 (by rfl) cert_18862

theorem cert_25817 : Represents 299 297 :=
  segment 35 299 297 334 208 (by rfl) cert_25782

theorem cert_25836 : Represents 300 298 :=
  segment 18 300 298 318 224 (by rfl) cert_25697

theorem cert_25838 : Represents 301 299 :=
  segment 1 301 299 302 296 (by rfl) cert_25445

theorem cert_25841 : Represents 302 300 :=
  segment 2 302 300 304 290 (by rfl) cert_19521

theorem cert_25869 : Represents 303 301 :=
  segment 27 303 301 330 54 (by rfl) cert_19294

theorem cert_25880 : Represents 304 302 :=
  segment 10 304 302 314 270 (by rfl) cert_25308

theorem cert_25890 : Represents 305 303 :=
  segment 9 305 303 314 142 (by rfl) cert_17108

theorem cert_25895 : Represents 306 304 :=
  segment 4 306 304 310 248 (by rfl) cert_15330

theorem cert_25919 : Represents 307 305 :=
  segment 23 307 305 330 278 (by rfl) cert_22279

theorem cert_25924 : Represents 308 306 :=
  segment 4 308 306 312 250 (by rfl) cert_25568

theorem cert_25946 : Represents 309 307 :=
  segment 21 309 307 330 22 (by rfl) cert_25417

theorem cert_25949 : Represents 542 448 :=
  segment 2 542 448 544 162 (by rfl) cert_24760

theorem cert_25965 : Represents 526 16 :=
  segment 16 526 16 542 448 (by rfl) cert_25949

theorem cert_26011 : Represents 480 354 :=
  segment 46 480 354 526 16 (by rfl) cert_25965

theorem cert_26019 : Represents 472 146 :=
  segment 8 472 146 480 354 (by rfl) cert_26011

theorem cert_26045 : Represents 446 224 :=
  segment 26 446 224 472 146 (by rfl) cert_26019

theorem cert_26075 : Represents 416 74 :=
  segment 30 416 74 446 224 (by rfl) cert_26045

theorem cert_26109 : Represents 382 368 :=
  segment 34 382 368 416 74 (by rfl) cert_26075

theorem cert_26123 : Represents 368 56 :=
  segment 14 368 56 382 368 (by rfl) cert_26109

theorem cert_26149 : Represents 342 272 :=
  segment 26 342 272 368 56 (by rfl) cert_26123

theorem cert_26163 : Represents 328 266 :=
  segment 14 328 266 342 272 (by rfl) cert_26149

theorem cert_26181 : Represents 310 308 :=
  segment 18 310 308 328 266 (by rfl) cert_26163

theorem cert_26183 : Represents 311 309 :=
  segment 1 311 309 312 306 (by rfl) cert_19312

theorem cert_26224 : Represents 312 310 :=
  segment 40 312 310 352 226 (by rfl) cert_17070

theorem cert_26232 : Represents 313 311 :=
  segment 7 313 311 320 130 (by rfl) cert_22701

theorem cert_26263 : Represents 314 312 :=
  segment 30 314 312 344 40 (by rfl) cert_22479

theorem cert_26272 : Represents 352 184 :=
  segment 8 352 184 360 128 (by rfl) cert_17409

theorem cert_26296 : Represents 328 138 :=
  segment 24 328 138 352 184 (by rfl) cert_26272

theorem cert_26309 : Represents 315 313 :=
  segment 13 315 313 328 138 (by rfl) cert_26296

theorem cert_26314 : Represents 316 314 :=
  segment 4 316 314 320 258 (by rfl) cert_25695

theorem cert_26321 : Represents 386 6 :=
  segment 6 386 6 392 384 (by rfl) cert_22120

theorem cert_26355 : Represents 352 290 :=
  segment 34 352 290 386 6 (by rfl) cert_26321

theorem cert_26390 : Represents 317 315 :=
  segment 35 317 315 352 290 (by rfl) cert_26355

theorem cert_26401 : Represents 318 316 :=
  segment 10 318 316 328 138 (by rfl) cert_26296

theorem cert_26403 : Represents 319 317 :=
  segment 1 319 317 320 314 (by rfl) cert_22503

theorem cert_26410 : Represents 320 318 :=
  segment 6 320 318 326 72 (by rfl) cert_18563

theorem cert_26432 : Represents 321 319 :=
  segment 21 321 319 342 0 (by rfl) (zero_represents 342)

theorem cert_26461 : Represents 322 320 :=
  segment 28 322 320 350 104 (by rfl) cert_25530

theorem cert_26469 : Represents 323 321 :=
  segment 7 323 321 330 150 (by rfl) cert_25685

theorem cert_26474 : Represents 324 322 :=
  segment 4 324 322 328 266 (by rfl) cert_26163

theorem cert_26486 : Represents 325 323 :=
  segment 11 325 323 336 122 (by rfl) cert_19288

theorem cert_26513 : Represents 326 324 :=
  segment 26 326 324 352 32 (by rfl) cert_24952

theorem cert_26547 : Represents 327 325 :=
  segment 33 327 325 360 50 (by rfl) cert_19465

theorem cert_26574 : Represents 342 216 :=
  segment 26 342 216 368 56 (by rfl) cert_26123

theorem cert_26588 : Represents 328 326 :=
  segment 14 328 326 342 216 (by rfl) cert_26574

theorem cert_26594 : Represents 329 327 :=
  segment 5 329 327 334 208 (by rfl) cert_25782

theorem cert_26607 : Represents 331 329 :=
  segment 11 331 329 342 272 (by rfl) cert_26149

theorem cert_26618 : Represents 332 330 :=
  segment 10 332 330 342 320 (by rfl) cert_112

theorem cert_26654 : Represents 333 331 :=
  segment 35 333 331 368 106 (by rfl) cert_19256

theorem cert_26657 : Represents 334 332 :=
  segment 2 334 332 336 322 (by rfl) cert_15304

theorem cert_26677 : Represents 335 333 :=
  segment 19 335 333 354 70 (by rfl) cert_25393

theorem cert_26686 : Represents 336 334 :=
  segment 8 336 334 344 8 (by rfl) cert_15296

theorem cert_26692 : Represents 337 335 :=
  segment 5 337 335 342 216 (by rfl) cert_26574

theorem cert_26699 : Represents 338 336 :=
  segment 6 338 336 344 90 (by rfl) cert_25403

theorem cert_26708 : Represents 438 248 :=
  segment 8 438 248 446 224 (by rfl) cert_26045

theorem cert_26778 : Represents 368 314 :=
  segment 70 368 314 438 248 (by rfl) cert_26708

theorem cert_26792 : Represents 354 62 :=
  segment 14 354 62 368 314 (by rfl) cert_26778

theorem cert_26807 : Represents 339 337 :=
  segment 15 339 337 354 62 (by rfl) cert_26792

theorem cert_26810 : Represents 340 338 :=
  segment 2 340 338 342 328 (by rfl) cert_22267

theorem cert_26822 : Represents 341 339 :=
  segment 11 341 339 352 184 (by rfl) cert_26272

theorem cert_26835 : Represents 342 340 :=
  segment 12 342 340 354 62 (by rfl) cert_26792

theorem cert_26838 : Represents 374 120 :=
  segment 2 374 120 376 104 (by rfl) cert_17393

theorem cert_26869 : Represents 343 341 :=
  segment 31 343 341 374 120 (by rfl) cert_26838

theorem cert_26876 : Represents 344 342 :=
  segment 6 344 342 350 96 (by rfl) cert_24954

theorem cert_26882 : Represents 345 343 :=
  segment 5 345 343 350 224 (by rfl) cert_25397

theorem cert_26889 : Represents 346 344 :=
  segment 6 346 344 352 98 (by rfl) cert_25663

theorem cert_26893 : Represents 347 345 :=
  segment 3 347 345 350 320 (by rfl) cert_17072

theorem cert_26898 : Represents 348 346 :=
  segment 4 348 346 352 290 (by rfl) cert_26355

theorem cert_26902 : Represents 349 347 :=
  segment 3 349 347 352 322 (by rfl) cert_22160

theorem cert_26911 : Represents 504 490 :=
  segment 8 504 490 512 490 (by rfl) cert_22000

theorem cert_26927 : Represents 488 274 :=
  segment 16 488 274 504 490 (by rfl) cert_26911

theorem cert_26967 : Represents 448 386 :=
  segment 40 448 386 488 274 (by rfl) cert_26927

theorem cert_26969 : Represents 446 320 :=
  segment 2 446 320 448 386 (by rfl) cert_26967

theorem cert_26999 : Represents 416 392 :=
  segment 30 416 392 446 320 (by rfl) cert_26969

theorem cert_27065 : Represents 350 348 :=
  segment 66 350 348 416 392 (by rfl) cert_26999

theorem cert_27074 : Represents 360 106 :=
  segment 8 360 106 368 314 (by rfl) cert_26778

theorem cert_27083 : Represents 351 349 :=
  segment 9 351 349 360 106 (by rfl) cert_27074

theorem cert_27090 : Represents 386 384 :=
  segment 6 386 384 392 138 (by rfl) cert_25082

theorem cert_27108 : Represents 368 154 :=
  segment 18 368 154 386 384 (by rfl) cert_27090

theorem cert_27124 : Represents 352 350 :=
  segment 16 352 350 368 154 (by rfl) cert_27108

theorem cert_27132 : Represents 353 351 :=
  segment 7 353 351 360 210 (by rfl) cert_18864

end Erdos261Finite
