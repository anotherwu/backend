package org.alex.platform.util;

import org.graalvm.polyglot.*;
import org.springframework.core.io.ClassPathResource;
import org.springframework.util.FileCopyUtils;

import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.io.IOException;

public class JavaScriptRSACall {
    public   String getRasresult(String str,String type) {
        // 定义输入参数
    /*    String str = "qwert666";
        String type = "login";

     */
        String key = "be24e372dc1b329633a6a014a7c02797915e3c363dd6ee119377bd645329b7e6446b4a71ac5f878ebc870c6d8bfd3c06b92e6c6e93390b34192a7a9e430800091761473fac2cc0a68a828b2589a8cb729c19161e8e27f4c0f3cde9701fafe48d2b65947799072afa6a3f2d7bdbef8b6d7429c2d115a3e5f723467d57b3ac6967";

        // 加载 JavaScript 文件内容
        String jsCode = readFile("RSAUtils.js");
        Value result = null;
        if (jsCode != null) {
            // 初始化 GraalVM 上下文
            try (Context context = Context.create()) {
                // 执行 JavaScript 代码
                context.eval("js", jsCode);

                // 调用 rsaBdg 函数并传入参数
                Value rsaUtils = context.eval("js", "RSAUtils");
                result = rsaUtils.invokeMember("rsaBdg", str, type, key);

                // 输出加密结果
                System.out.println("加密结果: " + result.asString());

                return result.asString();
            }
        }
        return result.asString();
    }

    // 加载 JS 文件内容的辅助方法
    private static String loadJSFile(String filePath) {
        try {
            return new String(Files.readAllBytes(Paths.get(filePath)));
        } catch (IOException e) {
            System.err.println("加载 JavaScript 文件失败: " + e.getMessage());
            return null;
        }
    }

    public static String readFile(String fileName){
        File file = null;
        String text = null;
        ClassPathResource cpr = new ClassPathResource("js/" + fileName);
        byte[] bdata = new byte[0];
        try {
            bdata = FileCopyUtils.copyToByteArray(cpr.getInputStream());
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        text = new String(bdata, StandardCharsets.UTF_8);
        return text;
    }
}
