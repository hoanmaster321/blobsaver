/*
 * Copyright (c) 2023  airsquared
 *
 * This file is part of blobsaver.
 *
 * blobsaver is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, version 3 of the License.
 *
 * blobsaver is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with blobsaver.  If not, see <https://www.gnu.org/licenses/>.
 */

package airsquared.blobsaver.app;

import com.google.gson.Gson;
import com.google.gson.JsonSyntaxException;
import javafx.concurrent.Task;

import javax.net.ssl.SSLContext;
import javax.net.ssl.TrustManager;
import javax.net.ssl.X509TrustManager;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.SecureRandom;
import java.security.cert.X509Certificate;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.StringJoiner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static airsquared.blobsaver.app.Utils.containsIgnoreCase;
import static airsquared.blobsaver.app.Utils.executeProgram;
import static airsquared.blobsaver.app.Utils.extractBuildManifest;
import static airsquared.blobsaver.app.Utils.getFirmwareList;
import static airsquared.blobsaver.app.Utils.getSignedBetas;
import static airsquared.blobsaver.app.Utils.getSignedFirmwares;
import static airsquared.blobsaver.app.Utils.isNumeric;

public class TSS extends Task<String> {

    private static final Pattern ipswURLPattern = Pattern.compile("(https?://|file:/).*\\.(ipsw|plist)");
    private static final Pattern versionPattern = Pattern.compile("[0-9]+\\.[0-9]+\\.?[0-9]*(?<!\\.)");
    private static final Pattern hex64Pattern = Pattern.compile("[0-9a-fA-F]{64}");
    private static final Pattern cryptexSeedPattern = Pattern.compile("(0x)?[0-9a-fA-F]{16,32}");

    /**
     * Default Cryptex1 nonce (all-zero seed SHA256: 0x00000000000000000000000000000000 -> 3f4fba536679e5a34cb2f9e656bca1cd704cc5490420807f10e82698ad9622e4)
     */
    public static final String DEFAULT_CRYPTEX1_NONCE = "3f4fba536679e5a34cb2f9e656bca1cd704cc5490420807f10e82698ad9622e4";

    private static final String[] CRYPTEX1_MANIFEST_KEYS = {
            "Cryptex1,ChipID",
            "Cryptex1,Type",
            "Cryptex1,SubType",
            "Cryptex1,ProductClass",
            "Cryptex1,UseProductClass",
            "Cryptex1,NonceDomain",
            "Cryptex1,Version",
            "Cryptex1,PreauthorizationVersion",
            "Cryptex1,FakeRoot"
    };

    private final String name;
    private final String deviceIdentifier;
    private final String ecid;
    private final String savePath;

    private final String boardConfig;

    private final boolean includeBetas;
    private final String manualVersion;
    private final String manualIpswURL;

    private final String apnonce, generator;

    private final boolean includeCryptex1;
    private final String cryptex1Nonce, cryptex1Seed;

    private final boolean saveToTSSSaver, saveToSHSHHost;

    /**
     * Private constructor; use {@link TSS.Builder} instead
     */
    private TSS(String name, String deviceIdentifier, String ecid, String savePath, String boardConfig,
                boolean includeBetas, String manualVersion, String manualIpswURL, String apnonce, String generator,
                boolean includeCryptex1, String cryptex1Nonce, String cryptex1Seed,
                boolean saveToTSSSaver, boolean saveToSHSHHost) {
        this.name = name;
        this.deviceIdentifier = deviceIdentifier;
        this.ecid = ecid;
        this.boardConfig = boardConfig;
        this.includeBetas = includeBetas;
        this.manualVersion = manualVersion;
        this.manualIpswURL = manualIpswURL;
        this.apnonce = apnonce;
        this.generator = generator;
        this.includeCryptex1 = includeCryptex1;
        this.cryptex1Nonce = cryptex1Nonce;
        this.cryptex1Seed = cryptex1Seed;
        this.saveToTSSSaver = saveToTSSSaver;
        this.saveToSHSHHost = saveToSHSHHost;
        this.savePath = parsePath(savePath);
    }

    /**
     * @return a printable multiline string describing the blobs saved
     * @throws TSSException if blobs were not saved successfully
     */
    @Override
    protected String call() throws TSSException {
        checkInputs();

        List<Utils.IOSVersion> iosVersions = getIOSVersions();
        System.out.println("iosVersions = " + iosVersions);
        ArrayList<String> args = constructArgs();

        var alreadySaved = new StringJoiner(", ");
        var newlySaved = new StringJoiner(", ");
        for (Utils.IOSVersion iosVersion : iosVersions) {
            if (!Prefs.getAlwaysSaveNewBlobs() && checkAlreadySaved(iosVersion)) {
                alreadySaved.add(iosVersion.versionString());
                continue;
            }

            try {
                saveFor(iosVersion, args);
            } catch (TSSException e) {
                if (manualVersion == null && manualIpswURL == null) {
                    var msg = e.getMessage();
                    if (msg.contains("not being signed")) {
                        System.err.println("Warning: ignoring unsigned version; API is likely out of date");
                        continue; // ignore not being signed (API might not be updated)
                    }
                    if ((msg.contains("Failed to load manifest") || msg.contains("Unable to extract BuildManifest"))
                            && includeBetas
                            && containsIgnoreCase(iosVersion.versionString(), "beta")
                            && iosVersion.ipswURL().contains("developer.apple")) {
                        System.err.println("Warning: ignoring developer beta");
                        continue;
                    }
                }
                throw e;
            }

            if (iosVersion.versionString() != null) {
                newlySaved.add(iosVersion.versionString());
            }
        }
        var responseBuilder = new StringBuilder();
        if (manualIpswURL != null || newlySaved.length() > 0) {
            responseBuilder.append("Successfully saved blobs in\n").append(savePath);
            if (newlySaved.length() > 0) {
                responseBuilder.append("\n\nFor version").append(iosVersions.size() == 1 ? " " : "s ").append(newlySaved);
            }
            if (alreadySaved.length() > 0) {
                responseBuilder.append("\n\n");
            }
        }
        if (alreadySaved.length() > 0) {
            responseBuilder.append("Already saved for ").append(alreadySaved);
        }

        if (saveToTSSSaver || saveToSHSHHost) {
            responseBuilder.append("\n\n");
        }
        if (saveToTSSSaver) {
            try {
                saveBlobsTSSSaver(responseBuilder);
            } catch (Exception e) {
                e.printStackTrace();
                responseBuilder.append("Error encountered while trying to save blobs to TSS Saver: ").append(e.getMessage());
            }
        }
        if (saveToSHSHHost) {
            try {
                saveBlobsSHSHHost(responseBuilder);
            } catch (Exception e) {
                e.printStackTrace();
                responseBuilder.append("Error encountered while trying to save blobs to SHSH Host: ").append(e.getMessage());
            }
        }

        Analytics.saveBlobs();
        return responseBuilder.toString();
    }

    private boolean checkAlreadySaved(Utils.IOSVersion ios) {
        if (ios.versionString() == null || apnonce == null) {
            return false;
        }
        var versionStringOnly = ios.versionString().trim().replaceFirst(" .*", ""); // strip out 'beta' labels
        // https://github.com/1Conan/tsschecker/blob/0bc6174c3c2f77a0de525b71e7d8ec0987f07aa1/tsschecker/tsschecker.c#L1262
        String fileName = parseECID() + "_" + deviceIdentifier + "_" + getBoardConfig() + "_" + versionStringOnly + "-" + ios.buildid() + "_" + apnonce + ".shsh2";
        Path shshPath = Path.of(parsePathWithVersion(ios), fileName);

        if (Files.exists(shshPath)) {
            if (includeCryptex1) {
                try {
                    String content = Files.readString(shshPath, StandardCharsets.UTF_8);
                    if (!content.contains("<key>Cryptex1,Ticket</key>")) {
                        return false;
                    }
                } catch (IOException e) {
                    return false;
                }
            }
            System.out.println("Already Saved: " + fileName);
            return true;
        }
        return false;
    }

    private long parseECID() {
        return isNumeric(ecid) ? Long.parseLong(ecid)
                : Long.parseLong(ecid.startsWith("0x") ? ecid.substring(2) : ecid, 16);
    }

    private String parsePath(String input) {
        if (!input.contains("${")) return input;
        String template = input;

        var variables = Map.of("${Name}", Utils.defIfNull(name, "UnknownName"),
                "${DeviceIdentifier}", deviceIdentifier,
                "${BoardConfig}", getBoardConfig(),
                "${APNonce}", Utils.defIfNull(apnonce, "UnknownAPNonce"),
                "${Generator}", Utils.defIfNull(generator, "UnknownGenerator"),
                "${DeviceModel}", Devices.identifierToModel(deviceIdentifier),
                "${ECID}", ecid);
        for (Map.Entry<String, String> entry : variables.entrySet()) {
            template = template.replace(entry.getKey(), entry.getValue());
        }
        return template;
    }

    private String parsePathWithVersion(Utils.IOSVersion ios) {
        if (!savePath.contains("${")) return savePath;
        String template = savePath;

        var majorVersion = ios.versionString() != null ? ios.versionString().replaceFirst("\\..*", "") : "UnknownVersion";
        var variables = Map.of(
                "${FullVersionString}", Utils.defIfNull(ios.versionString(), "UnknownVersion"),
                "${BuildID}", Utils.defIfNull(ios.buildid(), "UnknownBuildID"),
                "${MajorVersion}", majorVersion);
        for (Map.Entry<String, String> entry : variables.entrySet()) {
            template = template.replace(entry.getKey(), entry.getValue());
        }

        return template;
    }

    private void saveFor(Utils.IOSVersion iosVersion, ArrayList<String> args) throws TSSException {
        final int urlIndex = args.size() - 1;
        final int pathIndex = args.size() - 3;
        Path manifest;
        try {
            manifest = extractBuildManifest(iosVersion.ipswURL());
            args.set(urlIndex, manifest.toString());
        } catch (IOException e) {
            throw new TSSException("Unable to extract BuildManifest.", true, e);
        }
        Path targetDir = Path.of(parsePathWithVersion(iosVersion));
        try {
            args.set(pathIndex, targetDir.toString());
            Files.createDirectories(targetDir);
        } catch (IOException e) {
            throw new TSSException("Unable to create save directory. Try with a different save path. If you are using variables, make sure they are spelled correctly.", false, e);
        }
        try {
            System.out.println("Running: " + args);
            String tssLog = executeProgram(args, !includeCryptex1);
            if (includeCryptex1) {
                tssLog.lines()
                        .filter(l -> l.startsWith("[") || l.startsWith("Version:") || l.startsWith("Saved shsh") || l.startsWith("IS "))
                        .forEach(System.out::println);
            }
            parseTSSLog(tssLog);
            if (includeCryptex1) {
                injectCryptex1Ticket(manifest, tssLog, targetDir, iosVersion);
            }
        } catch (IOException e) {
            throw new TSSException("There was an error starting tsschecker.", true, e);
        } finally {
            deleteIfPossible(manifest);
        }
    }

    private void injectCryptex1Ticket(Path manifestPath, String tssLog, Path saveDir, Utils.IOSVersion iosVersion) throws TSSException {
        try {
            String manifestXml = Files.readString(manifestPath, StandardCharsets.UTF_8);
            if (!manifestXml.contains("<key>Cryptex1,")) {
                System.out.println("BuildManifest does not contain Cryptex1 components; skipping Cryptex1,Ticket.");
                return;
            }

            // Extract printed TSS request plist from tsschecker output
            Matcher reqMatcher = Pattern.compile("(<\\?xml version=\"1\\.0\" encoding=\"UTF-8\"\\?>[\\s\\S]*?</plist>)").matcher(tssLog);
            if (!reqMatcher.find()) {
                throw new TSSException("Unable to extract TSS request from tsschecker output for Cryptex1,Ticket.", true, tssLog);
            }
            String baseTssRequest = reqMatcher.group(1);

            long apChipId = extractIntegerKey(baseTssRequest, "ApChipID");
            long apBoardId = extractIntegerKey(baseTssRequest, "ApBoardID");
            long apEcid = extractIntegerKey(baseTssRequest, "ApECID");

            String buildIdentityXml = findMatchingBuildIdentity(manifestXml, apChipId, apBoardId);
            if (buildIdentityXml == null) {
                throw new TSSException("Could not find matching BuildIdentity in BuildManifest for Cryptex1,Ticket.", true, tssLog);
            }

            // Build Cryptex1,UDID (16 bytes: 8-byte big-endian ApChipID + 8-byte big-endian ApECID)
            byte[] udidBytes = ByteBuffer.allocate(16).putLong(apChipId).putLong(apEcid).array();
            String udidB64 = Base64.getEncoder().encodeToString(udidBytes);

            // Build Cryptex1,Nonce (32 bytes)
            String nonceHex = (cryptex1Nonce != null && !cryptex1Nonce.isBlank())
                    ? cryptex1Nonce.trim()
                    : DEFAULT_CRYPTEX1_NONCE;
            byte[] nonceBytes = HexFormat.of().parseHex(nonceHex);
            String nonceB64 = Base64.getEncoder().encodeToString(nonceBytes);

            var extraTags = new StringBuilder();
            extraTags.append("\t<key>@Cryptex1,Ticket</key>\n\t<true/>\n");
            extraTags.append("\t<key>Cryptex1,ProductionMode</key>\n\t<true/>\n");
            extraTags.append("\t<key>Cryptex1,UDID</key>\n\t<data>\n\t").append(udidB64).append("\n\t</data>\n");
            extraTags.append("\t<key>Cryptex1,Nonce</key>\n\t<data>\n\t").append(nonceB64).append("\n\t</data>\n");

            for (String key : CRYPTEX1_MANIFEST_KEYS) {
                if (!baseTssRequest.contains("<key>" + key + "</key>")) {
                    String kvXml = extractRawPlistKeyValue(buildIdentityXml, key);
                    if (kvXml != null) {
                        extraTags.append("\t").append(kvXml).append("\n");
                    }
                }
            }

            int lastDictClose = baseTssRequest.lastIndexOf("</dict>");
            if (lastDictClose < 0) {
                throw new TSSException("Malformed TSS request plist.", true, tssLog);
            }
            String cryptexTssRequest = baseTssRequest.substring(0, lastDictClose)
                    + extraTags
                    + baseTssRequest.substring(lastDictClose);

            String tssResponse = postAppleTSS(cryptexTssRequest);
            if (!tssResponse.contains("STATUS=0&MESSAGE=SUCCESS")) {
                throw new TSSException("Apple TSS refused Cryptex1,Ticket request: " + tssResponse, true, tssResponse);
            }

            Matcher ticketMatcher = Pattern.compile("(<key>Cryptex1,Ticket</key>\\s*<data>[\\s\\S]*?</data>)").matcher(tssResponse);
            if (!ticketMatcher.find()) {
                throw new TSSException("Apple TSS response did not contain Cryptex1,Ticket.", true, tssResponse);
            }
            String cryptexTicketEntry = ticketMatcher.group(1);

            Path shshFile = findSavedShshFile(saveDir, iosVersion);
            if (shshFile == null || !Files.exists(shshFile)) {
                throw new TSSException("Could not locate saved .shsh2 file to insert Cryptex1,Ticket.", true, tssLog);
            }

            String shshContent = Files.readString(shshFile, StandardCharsets.UTF_8);
            if (!shshContent.contains("<key>Cryptex1,Ticket</key>")) {
                shshContent = shshContent.replaceAll(
                        "(<key>ApImg4Ticket</key>\\s*<data>[\\s\\S]*?</data>)",
                        "$1\n\t" + Matcher.quoteReplacement(cryptexTicketEntry)
                );
            }
            if (cryptex1Seed != null && !cryptex1Seed.isBlank() && !shshContent.contains("<key>cryptex1Generator</key>")) {
                String normalizedSeed = cryptex1Seed.trim().startsWith("0x") ? cryptex1Seed.trim() : "0x" + cryptex1Seed.trim();
                shshContent = shshContent.replaceFirst(
                        "(<key>generator</key>\\s*<string>[^<]*</string>)",
                        "$1\n\t<key>cryptex1Generator</key>\n\t<string>" + Matcher.quoteReplacement(normalizedSeed) + "</string>"
                );
            }
            Files.writeString(shshFile, shshContent, StandardCharsets.UTF_8);
            System.out.println("Successfully injected Cryptex1,Ticket into " + shshFile.getFileName());
        } catch (IOException | InterruptedException e) {
            throw new TSSException("Failed to fetch or save Cryptex1,Ticket.", true, e);
        }
    }

    private Path findSavedShshFile(Path saveDir, Utils.IOSVersion iosVersion) throws IOException {
        String prefix = parseECID() + "_" + deviceIdentifier + "_" + getBoardConfig() + "_";
        if (iosVersion.versionString() != null && iosVersion.buildid() != null && apnonce != null) {
            var versionStringOnly = iosVersion.versionString().trim().replaceFirst(" .*", "");
            Path exact = saveDir.resolve(prefix + versionStringOnly + "-" + iosVersion.buildid() + "_" + apnonce + ".shsh2");
            if (Files.exists(exact)) {
                return exact;
            }
        }
        try (Stream<Path> files = Files.list(saveDir)) {
            return files
                    .filter(p -> p.getFileName().toString().startsWith(prefix) && p.getFileName().toString().endsWith(".shsh2"))
                    .max(Comparator.comparingLong(p -> p.toFile().lastModified()))
                    .orElse(null);
        }
    }

    private static long extractIntegerKey(String plistXml, String key) throws TSSException {
        Matcher m = Pattern.compile("<key>" + Pattern.quote(key) + "</key>\\s*<integer>\\s*([^<\\s]+)\\s*</integer>").matcher(plistXml);
        if (!m.find()) {
            throw new TSSException("Missing integer key " + key + " in TSS request.", true, plistXml);
        }
        return Long.parseLong(m.group(1));
    }

    private static String findMatchingBuildIdentity(String manifestXml, long apChipId, long apBoardId) {
        int idx = manifestXml.indexOf("<key>BuildIdentities</key>");
        if (idx < 0) return null;
        String sub = manifestXml.substring(idx);
        String[] parts = sub.split("<key>ApBoardID</key>");
        for (int i = 1; i < parts.length; i++) {
            String block = "<key>ApBoardID</key>" + parts[i];
            Long bId = extractHexOrIntString(block, "ApBoardID");
            Long cId = extractHexOrIntString(block, "ApChipID");
            if (bId != null && cId != null && bId == apBoardId && cId == apChipId) {
                return block;
            }
        }
        return parts.length > 1 ? "<key>ApBoardID</key>" + parts[1] : null;
    }

    private static Long extractHexOrIntString(String xml, String key) {
        Matcher m = Pattern.compile("<key>" + Pattern.quote(key) + "</key>\\s*<(?:string|integer)>\\s*([^<\\s]+)\\s*</(?:string|integer)>").matcher(xml);
        if (!m.find()) return null;
        String val = m.group(1);
        try {
            return val.startsWith("0x") || val.startsWith("0X")
                    ? Long.parseUnsignedLong(val.substring(2), 16)
                    : Long.parseLong(val);
        } catch (NumberFormatException e) {
            return null;
        }
    }

    private static String extractRawPlistKeyValue(String xml, String key) {
        Matcher m = Pattern.compile("(<key>" + Pattern.quote(key) + "</key>\\s*(?:<true/>|<false/>|<(?:string|integer|data)>[\\s\\S]*?</(?:string|integer|data)>))").matcher(xml);
        return m.find() ? m.group(1) : null;
    }

    private static String postAppleTSS(String requestXml) throws IOException, InterruptedException {
        HttpClient client;
        try {
            TrustManager[] trustAll = new TrustManager[]{
                    new X509TrustManager() {
                        @Override
                        public void checkClientTrusted(X509Certificate[] chain, String authType) {}
                        @Override
                        public void checkServerTrusted(X509Certificate[] chain, String authType) {}
                        @Override
                        public X509Certificate[] getAcceptedIssuers() { return new X509Certificate[0]; }
                    }
            };
            SSLContext sc = SSLContext.getInstance("TLS");
            sc.init(null, trustAll, new SecureRandom());
            client = HttpClient.newBuilder().sslContext(sc).build();
        } catch (Exception e) {
            client = HttpClient.newHttpClient();
        }

        HttpRequest request = HttpRequest.newBuilder(URI.create("https://gs.apple.com/TSS/controller?action=2"))
                .header("Content-Type", "text/xml; charset=\"utf-8\"")
                .header("User-Agent", "InetURL/1.0")
                .POST(HttpRequest.BodyPublishers.ofString(requestXml, StandardCharsets.UTF_8))
                .build();

        HttpResponse<String> response = client.send(request, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
        return response.body();
    }

    private void deleteIfPossible(Path file) {
        try {
            Files.deleteIfExists(file);
        } catch (IOException ignored) {
        }
    }

    private void checkInputs() throws TSSException {
        try {
            Devices.getDeviceType(deviceIdentifier);
        } catch (IllegalArgumentException e) {
            throw new TSSException("\"" + deviceIdentifier + "\" is not a valid identifier", false);
        }
        if (boardConfig == null && Devices.doesRequireBoardConfig(deviceIdentifier)) {
            throw new TSSException("A board configuration is required for this device.", false);
        }
        if (includeCryptex1 && cryptex1Nonce != null && !cryptex1Nonce.isBlank()
                && !hex64Pattern.matcher(cryptex1Nonce.trim()).matches()) {
            throw new TSSException("\"" + cryptex1Nonce + "\" is not a valid Cryptex1 Nonce", false);
        }
        if (includeCryptex1 && cryptex1Seed != null && !cryptex1Seed.isBlank()
                && !cryptexSeedPattern.matcher(cryptex1Seed.trim()).matches()) {
            throw new TSSException("\"" + cryptex1Seed + "\" is not a valid Cryptex1 Seed", false);
        }
        if (manualIpswURL != null) { // check URL
            try {
                if (!ipswURLPattern.matcher(manualIpswURL).matches()) {
                    throw new URISyntaxException(manualIpswURL, "Doesn't match ipsw URL regex");
                }
                new URI(manualIpswURL); // check URL
            } catch (URISyntaxException e) {
                throw new TSSException("The IPSW URL is not valid.\n\nMake sure it's a valid URL that ends with \".ipsw\" or \".plist\"", false, e);
            }
            if (manualIpswURL.startsWith("file:")) try {
                Path.of(new URI(manualIpswURL)).toRealPath(); // check URI
            } catch (IllegalArgumentException | URISyntaxException | IOException e) {
                throw new TSSException("The IPSW URL is not valid.\n\nMake sure it's a valid file URL to a local .ipsw or .plist file.", false, e);
            }
        } else if (manualVersion != null && !versionPattern.matcher(manualVersion).matches()) {
            throw new TSSException("Invalid version. Make sure it follows the convention X.X.X or X.X, like \"13.1\" or \"13.5.5\"", false);
        }
    }

    /**
     * Adds to the arraylists, depending on the fields {@link #manualIpswURL} and {@link #manualVersion}.
     * <p>
     * If both of those fields are null, it adds all signed versions.
     *
     * @return a list of {@link Utils.IOSVersion} to save blobs for
     */
    private List<Utils.IOSVersion> getIOSVersions() throws TSSException {
        try {
            if (manualVersion != null) {
                return Collections.singletonList(getFirmwareList(deviceIdentifier).filter(iosVersion ->
                                manualVersion.equals(iosVersion.versionString())).findFirst()
                        .orElseThrow(() -> new TSSException("No versions found.", false)));
            } else if (manualIpswURL != null) {
                return Collections.singletonList(new Utils.IOSVersion(null, null, manualIpswURL, null));
            } else if (includeBetas) {
                var signedFirmwares = getSignedFirmwares(deviceIdentifier);
                try {
                    Stream<Utils.IOSVersion> signedBetas = getSignedBetas(deviceIdentifier);
                    return Stream.concat(signedFirmwares, signedBetas).toList();
                } catch (Exception e) {
                    if (e.getMessage() != null && e.getMessage().startsWith("HTTP Response was (GET https://www.betahub.cn/api/")) {
                        throw new TSSException("There was an error retrieving beta versions; try disabling 'Include Betas'.\n\nThis is a known issue. See issue #614 on GitHub for more information or if you can help.", false, e);
                    }
                    throw new TSSException("There was an error retrieving beta versions; try disabling 'Include Betas'. For more information, try again with the debug log open.", false, e);
                }
            } else { // all signed firmwares
                return getSignedFirmwares(deviceIdentifier).toList();
            }
        } catch (FileNotFoundException e) {
            var message = "The device \"" + deviceIdentifier + "\" could not be found.";
            if (includeBetas) {
                message += " This device may not have any beta versions available; try disabling 'Include Betas'.";
            }
            throw new TSSException(message, false, e);
        } catch (IOException e) {
            var message = "Saving blobs failed. Check your internet connection.";
            throw new TSSException(message, false, e);
        }
    }

    private ArrayList<String> constructArgs() {
        var args = new ArrayList<String>(18);
        String tsscheckerPath = Utils.getTsschecker().getAbsolutePath();
        Collections.addAll(args, tsscheckerPath, "--nocache", "--save", "--device", deviceIdentifier, "--ecid", ecid);
        Collections.addAll(args, "--boardconfig", getBoardConfig());
        if (apnonce != null) {
            Collections.addAll(args, "--apnonce", apnonce);
            if (generator != null) {
                Collections.addAll(args, "--generator", generator);
            }
        } else {
            Collections.addAll(args, "--generator", "0x1111111111111111");
        }
        if (includeCryptex1) {
            args.add("--print-tss-request");
        }

        Collections.addAll(args, "--save-path", "will be replaced in loop",
                "--build-manifest", "will be replaced in loop");

        return args;
    }

    private String getBoardConfig() {
        return Utils.defIfNull(boardConfig, Devices.getBoardConfig(deviceIdentifier));
    }

    private void parseTSSLog(String tsscheckerLog) throws TSSException {
        if (containsIgnoreCase(tsscheckerLog, "Saved shsh blobs")) {
            return; // success
        } else if (containsIgnoreCase(tsscheckerLog, "[Error] [TSSC] manually specified ecid=" + ecid + ", but parsing failed")) {
            throw new TSSException("\"" + ecid + "\" is not a valid ECID. Try using the 'Read from device' button.", false);
        } else if (containsIgnoreCase(tsscheckerLog, "[Error] [TSSC] manually specified ApNonce=" + apnonce + ", but parsing failed")
                || containsIgnoreCase(tsscheckerLog, "[Error] [TSSR] parsed APNoncelen != requiredAPNoncelen")) {
            throw new TSSException("\"" + apnonce + "\" is not a valid APNonce", false);
        } else if (containsIgnoreCase(tsscheckerLog, "could not get BuildIdentity for installType=Erase")
                && containsIgnoreCase(tsscheckerLog, "could not get BuildIdentity for installType=Update")
                && containsIgnoreCase(tsscheckerLog, "checking tss status failed")) {
            throw new TSSException("Saving blobs failed. Check the board configuration or try again later.", true, tsscheckerLog);
        } else if (containsIgnoreCase(tsscheckerLog, "Could not resolve host")) {
            throw new TSSException("Saving blobs failed. Check your internet connection.", false, tsscheckerLog);
        } else if (containsIgnoreCase(tsscheckerLog, "can't save shsh at")) {
            throw new TSSException("'" + savePath + "' is not a valid path. If you are using variables, make sure they are spelled correctly.", false);
        } else if (containsIgnoreCase(tsscheckerLog, "IS NOT being signed")) {
            if (manualVersion == null) {
                throw new TSSException("The " + Devices.getOSNameForType(Devices.getDeviceType(deviceIdentifier)) + " version is not being signed for device " + deviceIdentifier, false);
            } else {
                throw new TSSException("%s %s is not being signed for device %s".formatted(
                        Devices.getOSNameForIdentifier(deviceIdentifier), manualVersion, deviceIdentifier), false);
            }

        } else if (containsIgnoreCase(tsscheckerLog, "failed to load manifest")) {
            if (manualIpswURL != null) {
                throw new TSSException("Failed to load manifest. The IPSW or build manifest URL is not valid.\n\n", false);
            } else {
                throw new TSSException("Failed to load manifest.", true, tsscheckerLog); // this exact message is used elsewhere; do not modify
            }
        } else if (containsIgnoreCase(tsscheckerLog, "selected device can't be used with that buildmanifest")) {
            throw new TSSException("Device and build manifest don't match.", false);
        }
        throw new TSSException("An unknown error occurred.", true, tsscheckerLog);
    }

    @SuppressWarnings("UnusedReturnValue")
    public static class Builder {
        private String name, device, ecid, savePath, boardConfig, manualVersion, manualIpswURL, apnonce, generator;
        private String cryptex1Nonce, cryptex1Seed;
        private boolean includeCryptex1 = true;
        private boolean includeBetas, saveToTSSSaver, saveToSHSHHost;

        public Builder setName(String name) {
            this.name = name;
            return this;
        }

        public Builder setDevice(String device) {
            this.device = device;
            return this;
        }

        public Builder setEcid(String ecid) {
            this.ecid = ecid;
            return this;
        }

        public Builder setSavePath(String savePath) {
            this.savePath = savePath;
            return this;
        }

        public Builder setBoardConfig(String boardConfig) {
            this.boardConfig = boardConfig;
            return this;
        }

        public Builder setManualVersion(String manualVersion) {
            manualIpswURL = null;
            this.manualVersion = manualVersion;
            return this;
        }

        public Builder setManualIpswURL(String manualIpswURL) {
            manualVersion = null;
            this.manualIpswURL = manualIpswURL;
            return this;
        }

        public Builder setApnonce(String apnonce) {
            this.apnonce = apnonce;
            return this;
        }

        public Builder setGenerator(String generator) {
            this.generator = generator;
            return this;
        }

        public Builder setIncludeCryptex1(boolean includeCryptex1) {
            this.includeCryptex1 = includeCryptex1;
            return this;
        }

        public Builder setCryptex1Nonce(String cryptex1Nonce) {
            this.cryptex1Nonce = cryptex1Nonce;
            return this;
        }

        public Builder setCryptex1Seed(String cryptex1Seed) {
            this.cryptex1Seed = cryptex1Seed;
            return this;
        }

        public Builder setIncludeBetas(boolean includeBetas) {
            this.includeBetas = includeBetas;
            return this;
        }

        public Builder saveToTSSSaver(boolean saveToTSSSaver) {
            this.saveToTSSSaver = saveToTSSSaver;
            return this;
        }

        public Builder saveToSHSHHost(boolean saveToSHSHHost) {
            this.saveToSHSHHost = saveToSHSHHost;
            return this;
        }

        public TSS build() {
            return new TSS(name,
                    Objects.requireNonNull(device, "Device"),
                    Objects.requireNonNull(ecid, "ECID"),
                    Objects.requireNonNull(savePath, "Save Path"),
                    boardConfig, includeBetas, manualVersion, manualIpswURL, apnonce, generator,
                    includeCryptex1, cryptex1Nonce, cryptex1Seed, saveToTSSSaver, saveToSHSHHost);
        }
    }


    /**
     * Checked exception for all TSS related errors.
     */
    public static class TSSException extends Exception {

        public final String tssLog;
        public final boolean isReportable;

        public TSSException(String message, boolean isReportable) {
            super(message);
            this.isReportable = isReportable;
            this.tssLog = null;
        }

        public TSSException(String message, boolean isReportable, String tssLog) {
            super(message);
            this.isReportable = isReportable;
            this.tssLog = tssLog;
        }

        public TSSException(String message, boolean isReportable, Throwable cause) {
            super(message, cause);
            this.isReportable = isReportable;
            this.tssLog = null;
        }

        public void showErrorAlert() {
            if (isReportable && tssLog != null) {
                Utils.showReportableError(getMessage(), tssLog);
            } else if (isReportable) {
                Utils.showReportableError(getMessage(), Utils.exceptionToString(this));
            } else {
                Utils.showUnreportableError(getMessage());
            }
        }
    }

    private void saveBlobsTSSSaver(StringBuilder responseBuilder) throws IOException, InterruptedException {
        var deviceParameters = new HashMap<>();

        deviceParameters.put("ecid", String.valueOf(parseECID()));
        deviceParameters.put("deviceIdentifier", deviceIdentifier);
        deviceParameters.put("boardConfig", getBoardConfig());

        if (generator != null) {
            deviceParameters.put("generator", generator);
        }
        if (apnonce != null) {
            deviceParameters.put("apnonce", apnonce);
        }

        System.out.println(deviceParameters);
        var headers = new HashMap<String, String>();
        headers.put("Content-Type", "application/x-www-form-urlencoded");

        HttpResponse<String> response =
                Network.makePOSTRequest("https://tsssaver.1conan.com/v2/api/save.php", deviceParameters, headers, true);
        System.out.println(response.body());

        Map responseBody;
        try {
            responseBody = new Gson().fromJson(response.body(), Map.class);
        } catch (JsonSyntaxException e) {
            responseBuilder.append("Error encountered while trying to save blobs to TSSSaver: ").append(response.body())
                    .append("\nThis is likely an issue with the third-party service, not blobsaver.");
            return;
        }

        if (responseBody == null) {
            responseBuilder.append("Error encountered while trying to save blobs to TSSSaver: ").append("Response code=").append(response.statusCode());
        } else if (responseBody.containsKey("errors")) {
            responseBuilder.append("Error encountered while trying to save blobs to TSSSaver: ").append(responseBody.get("errors"));
        } else {
            responseBuilder.append("Also saved blobs online to TSS Saver.");
        }
    }

    private void saveBlobsSHSHHost(StringBuilder responseBuilder) throws IOException, InterruptedException {
        if (saveToTSSSaver) {
            responseBuilder.append("\n");
        }

        var deviceParameters = new HashMap<>();

        deviceParameters.put("ecid", ecid);
        deviceParameters.put("boardconfig", getBoardConfig());
        deviceParameters.put("device", deviceIdentifier);
        deviceParameters.put("selected_firmware", "All");

        if (generator != null) {
            deviceParameters.put("generator", generator);
        }
        if (apnonce != null) {
            deviceParameters.put("apnonce", apnonce);
        }

        System.out.println(deviceParameters);
        String userAgent = "Blobsaver " + Main.appVersion;
        var headers = new HashMap<String, String>();
        headers.put("Content-Type", "application/x-www-form-urlencoded");
        headers.put("User-Agent", userAgent);
        headers.put("X-CPU-STATE", "0000000000000000000000000000000000000000");

        HttpResponse<String> response =
                Network.makePOSTRequest("https://api.arx8x.net/shsh3/", deviceParameters, headers, false);
        System.out.println(response.body());

        Map responseBody;
        try {
            responseBody = new Gson().fromJson(response.body(), Map.class);
        } catch (JsonSyntaxException e) {
            responseBuilder.append("Error encountered while trying to save blobs to SHSH Host: ").append(response.body())
                    .append("\nThis is likely an issue with the third-party service, not blobsaver.");
            return;
        }

        if (responseBody.get("code").equals((double) 0)) {
            responseBuilder.append("Also saved blobs online to SHSH Host.");
        } else {
            responseBuilder.append("Error encountered while trying to save blobs to SHSH Host: ").append(responseBody.get("message"));
        }
    }
}
