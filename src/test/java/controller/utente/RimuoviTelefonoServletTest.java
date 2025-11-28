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

    @Test
    void testDoPost_PhoneRemovalFromSessionList() throws ServletException, IOException {
        // Test per verificare che il telefono viene rimosso dalla lista di sessione
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"12345\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("12345", "98765"));

        // Add multiple phones to session list
        telefoniList.add("12345");
        telefoniList.add("98765");
        telefoniList.add("55555");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verify that the phone was removed from the session list (cattura SURVIVED su loop condition)
        assertEquals(2, telefoniList.size(), "Telefono dovrebbe essere rimosso dalla lista");
        assertFalse(telefoniList.contains("12345"), "Telefono rimosso non dovrebbe essere nella lista");
        assertTrue(telefoniList.contains("98765"), "Gli altri telefoni dovrebbero rimanere");
        assertTrue(telefoniList.contains("55555"), "Gli altri telefoni dovrebbero rimanere");
    }

    @Test
    void testDoPost_FirstPhoneInList() throws ServletException, IOException {
        // Test con il telefono come primo elemento della lista
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"FIRST\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("FIRST"));

        telefoniList.add("FIRST");
        telefoniList.add("SECOND");
        telefoniList.add("THIRD");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verify first phone was removed (cattura negated conditional su i=0)
        assertEquals(2, telefoniList.size());
        assertFalse(telefoniList.contains("FIRST"));
        assertTrue(telefoniList.contains("SECOND"));
    }

    @Test
    void testDoPost_MiddlePhoneInList() throws ServletException, IOException {
        // Test con il telefono nel mezzo della lista
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"MIDDLE\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("MIDDLE"));

        telefoniList.add("FIRST");
        telefoniList.add("MIDDLE");
        telefoniList.add("LAST");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verify middle phone was removed (cattura boundary condition su i < size)
        assertEquals(2, telefoniList.size());
        assertTrue(telefoniList.contains("FIRST"));
        assertFalse(telefoniList.contains("MIDDLE"));
        assertTrue(telefoniList.contains("LAST"));
    }

    @Test
    void testDoPost_LastPhoneInList() throws ServletException, IOException {
        // Test con il telefono come ultimo elemento
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"LAST\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("LAST"));

        telefoniList.add("FIRST");
        telefoniList.add("MIDDLE");
        telefoniList.add("LAST");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verify last phone was removed (cattura boundary condition e loop)
        assertEquals(2, telefoniList.size());
        assertTrue(telefoniList.contains("FIRST"));
        assertTrue(telefoniList.contains("MIDDLE"));
        assertFalse(telefoniList.contains("LAST"));
    }

    @Test
    void testDoPost_ResponseHeadersVerified() throws ServletException, IOException {
        // Test per verificare che setContentType e setCharacterEncoding vengono chiamati
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"12345\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("12345"));
        telefoniList.add("12345");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verifica che setContentType viene chiamato (cattura SURVIVED su removed call)
        verify(response).setContentType("text/plain");
        
        // Verifica che setCharacterEncoding viene chiamato (cattura SURVIVED su removed call)
        verify(response).setCharacterEncoding("UTF-8");
        
        pw.flush();
        String out = sw.toString();
        assertTrue(out.contains("Telefono rimosso con successo."));
    }

    @Test
    void testDoPost_PhoneNotInSessionList() throws ServletException, IOException {
        // Test quando il telefono non è nella lista di sessione ma è nel DB
        String json = "{\"email\":\"test@example.com\",\"telefono\":\"NOT_IN_SESSION\"}";
        when(request.getInputStream()).thenReturn(toServletInputStream(json));

        when(utenteDAOMock.cercaTelefoni("test@example.com")).thenReturn(List.of("NOT_IN_SESSION", "OTHER"));

        telefoniList.add("OTHER");
        telefoniList.add("ANOTHER");

        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        when(response.getWriter()).thenReturn(pw);

        servletUnderTest.doPost(request, response);

        // Verify that session list is unchanged (cattura negated conditional su equals)
        assertEquals(2, telefoniList.size());
        assertTrue(telefoniList.contains("OTHER"));
        assertTrue(telefoniList.contains("ANOTHER"));
    }
}
