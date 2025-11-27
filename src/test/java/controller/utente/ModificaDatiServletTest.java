package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.*;

class ModificaDatiServletTest {
    private ModificaDatiServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private UtenteDAO utenteDAOMock;
    private Utente utenteMock;
    private List<String> telefoniList;

    @BeforeEach
    void setUp() {
        servletUnderTest = new ModificaDatiServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utenteDAOMock = mock(UtenteDAO.class);
        utenteMock = mock(Utente.class);
        telefoniList = new ArrayList<>();

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
        // return same mutable list when getTelefoni() called
        when(utenteMock.getTelefoni()).thenReturn(telefoniList);

        servletUnderTest.setUtenteDAO(utenteDAOMock);
    }

    @Test
    void testDoGet_MissingParams_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn(null);
        when(request.getParameterValues("telefono")).thenReturn(null);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/errorForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_UpdateSuccess_CallsUpdateAndForwards() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("NuovoNome");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12345"});

        // utenteMock.getTelefoni() returns telefoniList (initially empty)
        servletUnderTest.doGet(request, response);

        // telefono should have been added
        assert telefoniList.contains("12345");
        // updateUtente should be invoked with the mock utente
        verify(utenteDAOMock).updateUtente(utenteMock);
        // session attribute should be updated
        verify(session).setAttribute("utente", utenteMock);
        // forwarded to support page
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_NomeUtenteNull_TelefoniProvided_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn(null);
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12345"});

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/errorForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_TelefoniNull_NomeUtenteProvided_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("MarioRossi");
        when(request.getParameterValues("telefono")).thenReturn(null);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/errorForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_EmptyNomeUtente_NotUpdated() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12345"});

        servletUnderTest.doGet(request, response);

        // nomeUtente should NOT be set (because it's empty)
        verify(utenteMock, never()).setNomeUtente(anyString());
        // telefono should still be added
        assert telefoniList.contains("12345");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_EmptyTelefono_NotAdded() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("NewName");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{""});

        servletUnderTest.doGet(request, response);

        // Empty telefono should NOT be added
        assertEquals(0, telefoniList.size(), "Empty telefono should not be added");
        verify(utenteMock).setNomeUtente("NewName");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_DuplicateTelefono_NotAdded() throws ServletException, IOException {
        // User already has telefono "12345"
        telefoniList.add("12345");

        when(request.getParameter("nomeUtente")).thenReturn("NomeCognome");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"12345"});

        servletUnderTest.doGet(request, response);

        // telefono "12345" should NOT be added again
        assertEquals(1, telefoniList.size(), "Duplicate telefono should not be added");
        verify(utenteMock).setNomeUtente("NomeCognome");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_MultipleTelefoni_OnlyNewOnesAdded() throws ServletException, IOException {
        // User already has "11111"
        telefoniList.add("11111");

        when(request.getParameter("nomeUtente")).thenReturn("TestUser");
        // Sending: existing "11111", new "22222", empty "", new "33333"
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"11111", "22222", "", "33333"});

        servletUnderTest.doGet(request, response);

        // Should have: 11111 (original), 22222 (new), 33333 (new)
        // Empty string and duplicate should be ignored
        assertEquals(3, telefoniList.size());
        assert telefoniList.contains("11111");
        assert telefoniList.contains("22222");
        assert telefoniList.contains("33333");

        verify(utenteMock).setNomeUtente("TestUser");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoGet_EmptyTelefoniArray_BoundaryCondition() throws ServletException, IOException {
        // Test the boundary condition where telefoni.length = 0
        when(request.getParameter("nomeUtente")).thenReturn("TestUser");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{});

        servletUnderTest.doGet(request, response);

        // With empty array, no telefono should be added
        assertEquals(0, telefoniList.size(), "No telefono should be added from empty array");
        verify(utenteMock).setNomeUtente("TestUser");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }

    @Test
    void testDoPost_CallsDoGet() throws ServletException, IOException {
        when(request.getParameter("nomeUtente")).thenReturn("PostTestUser");
        when(request.getParameterValues("telefono")).thenReturn(new String[]{"99999"});

        servletUnderTest.doPost(request, response);

        // Verify that doPost delegates to doGet
        assert telefoniList.contains("99999");
        verify(utenteMock).setNomeUtente("PostTestUser");
        verify(utenteDAOMock).updateUtente(utenteMock);
        verify(request).getRequestDispatcher("modifica-dati-supporto");
        verify(dispatcher).forward(request, response);
    }
}
