package controller.utente;

import jakarta.servlet.ReadListener;
import jakarta.servlet.ServletInputStream;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

class RimuoviTelefonoServletTest {
    private RimuoviTelefonoServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private UtenteDAO utenteDAOMock;
    private Utente utenteMock;
    private List<String> telefoniList;

    @BeforeEach
    void setUp() {
        servletUnderTest = new RimuoviTelefonoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        utenteDAOMock = mock(UtenteDAO.class);
        utenteMock = mock(Utente.class);
        telefoniList = new ArrayList<>();

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(utenteMock.getTelefoni()).thenReturn(telefoniList);

        servletUnderTest.setUtenteDAO(utenteDAOMock);
    }

    // helper to create a ServletInputStream from a string
    private ServletInputStream toServletInputStream(String str) {
        final InputStream byteStream = new ByteArrayInputStream(str.getBytes(StandardCharsets.UTF_8));
        return new ServletInputStream() {
            @Override
            public boolean isFinished() {
                try { return byteStream.available() == 0; } catch (IOException e) { return true; }
            }

            @Override
            public boolean isReady() { return true; }

            @Override
            public void setReadListener(ReadListener readListener) { }

            @Override
            public int read() throws IOException { return byteStream.read(); }
        };
    }

    @Test
    void testDoPost_RemovePhoneSuccess() throws ServletException, IOException {
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"12345\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        // DAO returns list containing telefono
        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("12345"));

        // session user has the telefono in list
        telefoniList.add("12345");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // verify DAO delete called
        verify(utenteDAOMock).deleteTelefono("test@example.com", "12345");
        // verify session attribute updated
        verify(session).setAttribute("utente", utenteMock);
        pw.flush();
        String out = sw.toString();
        assertTrue(out.contains("Telefono rimosso con successo."));
    }

    @Test
    void testDoPost_PhoneNotInDb_NoDeleteButSessionUpdated() throws ServletException, IOException {
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"99999\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        // DAO returns list without telefono
        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("12345"));

        // session user has telefono 99999
        telefoniList.add("99999");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // deleteTelefono should NOT be called because DAO list doesn't contain 99999
        verify(utenteDAOMock, never()).deleteTelefono(anyString(), anyString());
        // session should still be updated (telefono removed from session list)
        verify(session).setAttribute("utente", utenteMock);
        pw.flush();
        String out = sw.toString();
        assertTrue(out.contains("Telefono rimosso con successo."));
    }

    @Test
    void testDoPost_MalformedJson_ReturnsBadRequest() throws ServletException, IOException {
        String badJson = "not a json";
        when(request.getInputStream()).thenReturn(toServletInputStream(badJson));

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // should set status 400 and write error message
        verify(response).setStatus(HttpServletResponse.SC_BAD_REQUEST);
        pw.flush();
        String out = sw.toString();
        assertTrue(out.contains("Errore nella lettura del JSON."));
    }
}
